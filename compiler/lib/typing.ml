open ProgramRep
open Exceptions
open Absyn
open Helpers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let to_string_map lst f_key f_value =
  let rec aux lst map = match lst with
    | [] -> map
    | h::t -> aux t (StringMap.add (f_key h) (f_value h) map)
  in
  aux lst StringMap.empty

let rec type_equal type1 type2 =
  Printf.printf "eq: %s vs. %s\n" (type_string type1) (type_string type2);
  let aux t1 t2 =
    match (t1, t2) with
    | (T_Int, T_Int) -> true
    | (T_Bool, T_Bool) -> true
    | (T_Char, T_Char) -> true
    | (T_Array at1, T_Array at2) -> type_equal (Option.get at1) (Option.get at2)
    | (T_Struct(n1,ta1), T_Struct(n2, ta2)) when n1 = n2 && (List.length ta1) = (List.length ta2) -> true && (List.fold_right (fun e acc -> (type_equal (Option.get (fst e)) (Option.get (snd e))) && acc) (List.combine ta1 ta2) true)
    | (T_Null, _) -> true
    | (T_Generic c1, T_Generic c2) -> c1 = c2
    | (T_Routine(_,types1), T_Routine(_,types2)) -> 
      if List.length types1 = List.length types2 
      then 
        let extract_type = fun (vm,ty_opt) -> (vm, Option.get ty_opt) in
        List.fold_right (fun ((_,t1),(_,t2)) acc -> type_equal t1 t2 && acc) (List.combine (List.map extract_type types1) (List.map extract_type types2)) true 
      else false
    | _ -> false
  in aux type1 type2 || aux type2 type1

let rec first_non_null typs =
  match typs with
  | [] -> (Open, Error "No non-null type in array")
  | (_,Ok T_Null)::t -> first_non_null t
  | h::_ -> h

let type_array_literal lst =
  let rec aux_type ty vmod li =
    match li with
    | [] -> (vmod, Ok(ty))
    | (expr_vmod,Ok h)::t -> (
      if not (type_equal h ty) then raise_failure "Array literal containing expressions of non-equatable types"
      else aux_type ty (strictest_mod vmod expr_vmod) t
      )
    | (_,_)::_ -> vmod, Error "awww"
  in 
  let (vm,res) = first_non_null lst in
    if Result.is_ok res 
    then (let ty = Result.get_ok res in aux_type ty vm lst) 
    else (vm,res)

let default_value t =
  match t with
  | T_Int -> Value (Int 0)
  | T_Bool -> Value (Bool false)
  | T_Char -> Value (Char '0')
  | _ -> Reference (Null)

let simple_type t =
  match t with
    | T_Int | T_Bool | T_Char -> true
    | _ -> false

let rec translate_operational_type op_typ =
  match op_typ with
  | NOp_T t -> t
  | BinOp_T(op, ot1, ot2) -> ( match op, (translate_operational_type ot1), (translate_operational_type ot2) with
    | "&&", T_Bool, T_Bool -> T_Bool
    | "||", T_Bool, T_Bool -> T_Bool
    | "=", _, T_Null -> T_Bool
    | "=", T_Null, _ -> T_Bool
    | "=", t1, t2 when type_equal t1 t2 -> T_Bool
    | "!=", _, T_Null -> T_Bool
    | "!=", T_Null, _ -> T_Bool
    | "!=", T_Bool, T_Bool -> T_Bool
    | "!=", T_Char, T_Char -> T_Bool
    | "!=", T_Int, T_Int -> T_Bool
    | "<=", T_Int, T_Int -> T_Bool
    | "<", T_Int, T_Int -> T_Bool
    | ">=", T_Int, T_Int -> T_Bool
    | ">", T_Int, T_Int -> T_Bool
    | "+", T_Int, T_Int -> T_Int
    | "-", T_Int, T_Int -> T_Int
    | "/", T_Int, T_Int -> T_Int
    | "%", T_Int, T_Int -> T_Int
    | "*", T_Int, T_Int -> T_Int
    | _,t1,t2 -> raise_failure ("Unknown binary operation: '"^type_string t1^" "^op^" "^type_string t2^"'")
  )
  | UnOp_T(op, ot) -> ( match op, (translate_operational_type ot) with
    | "!", T_Bool -> T_Bool
    | "$", t -> t
    | _,t1 -> raise_failure ("Unknown unary operation: '"^op^" "^type_string t1^"'")
  )
  | TernaryOp_T(_,_,t) -> translate_operational_type t

let has_generic ts =
  List.fold_left (fun acc t -> match t with
  | T_Generic _ -> true
  | _ -> acc
  ) false ts

let routine_signature_equal (params1 : (var_mod * typ * string) list) params2 : bool =
  let rec aux params =
    match params with
    | [] -> true
    | ((vm1,t1,_),(vm2,t2,_))::t -> if (type_equal t1 t2) && (vm1 = vm2) then aux t else false
  in
  if (List.length params1 == List.length params2) then aux (List.combine params1 params2) else false
  
let rec type_expr expr env contexts : var_mod * (op_typ, string) result =
  match expr with
  | Reference ref_expr -> ( match type_reference ref_expr env contexts with 
    | (vm,Ok(t)) -> (vm, Ok(NOp_T t))
    | (vm,Error m) -> (vm,Error m)
  )
  | Value val_expr -> type_value val_expr env contexts
  | Ternary(cond,exp1,exp2) -> (
    let (_,cond_typ) = type_expr cond env contexts in
    match cond_typ with
    | Ok(op_typ) -> ( match translate_operational_type op_typ with
      | T_Bool -> (
        let (vm1,typ_res_1) = type_expr exp1 env contexts in
        let (vm2,typ_res_2) = type_expr exp2 env contexts in
        match typ_res_1, typ_res_2 with
        | _, Error msg
        | Error msg, _ -> (Open, Error msg)
        | Ok(ot1), Ok(ot2) -> (
          if not(type_equal (translate_operational_type ot1) (translate_operational_type ot2)) then raise_failure "Type mismatch in ternary" 
          else (strictest_mod vm1 vm2, Ok(TernaryOp_T(op_typ, ot1, ot2)))
        )
      )
      | _ -> raise_failure "Condition of ternary was not a boolean"
    )
    | Error msg -> (Open, Error msg)
  )

and type_inner_reference iref env contexts : var_mod * (typ, string) result =
  match iref with
  | Access name -> (var_modifier name env, var_type name env) 
  | StructAccess (refer, field) -> (
    let (vmod, typ_res) = type_inner_reference refer env contexts in
    match typ_res with
    | Error _ -> (vmod, typ_res)
    | Ok ty -> (
      match ty with 
      | T_Struct (str_name, typ_args) -> (match lookup_struct str_name env.var_env.structs with
      | Some (typ_vars, fields) -> (
        match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) fields) typ_vars typ_args with
        | Ok resolved_fields -> (
          let (field_mod, field_ty,_) = struct_field field (List.map (fun ((a,b),c) -> (a,b,c)) (List.combine resolved_fields (List.map (fun (_,_,n) -> n) fields))) in
          ((if vmod = Open then field_mod else Const), Ok (Option.get field_ty))
        )
        | Error m -> raise_failure (m^"inner stuff")
      )
      | None -> raise_failure ("No such struct '" ^ str_name ^ "'")
      )
      | _ -> raise_failure ("Field access of non-struct value")
    )
  )
  | ArrayAccess (refer, index) -> (
    let (vm,typ_res) = type_expr index env contexts in
    match typ_res with
    | Error m -> (vm,Error m)
    | Ok ot -> (
      match translate_operational_type ot with
      | T_Int -> (
        let (vmod, typ_res) = type_inner_reference refer env contexts in
        match typ_res with
        | Error _ -> (vmod, typ_res)
        | Ok ty -> ( match ty with 
          | T_Array array_typ -> (vmod, Ok (Option.get array_typ))
          | _ -> raise_failure ("Array access of non-array value")
        )
      )
      | _ -> raise_failure ("Array indexed with non-integer value")
    )
  )

and type_reference ref_expr env contexts : var_mod * (typ, string) result =
  match ref_expr with
  | Null -> (Open, Ok T_Null)
  | LocalContext(ref) -> type_inner_reference ref env contexts
  | OtherContext(cn,ref) -> ( match lookup_context cn env.file_refs contexts with
    | None -> failwith ("No such context: " ^ cn)
    | Some(env) -> type_inner_reference ref env contexts
  )

and type_value val_expr env contexts : var_mod * (op_typ, string) result =
  match val_expr with
  | Binary_op (op, expr1, expr2) -> (
    let (_, ty1) = type_expr expr1 env contexts in
    let (_, ty2) = type_expr expr2 env contexts in
    match ty1, ty2 with
    | Ok(ot1), Ok(ot2) -> (Open, Ok(BinOp_T(op, ot1, ot2)))
    | Error m, _
    | _, Error m -> (Open,Error m)
  )
  | Unary_op (op, expr) -> (
    let (_, ty) = type_expr expr env contexts in
    match ty with
    | Ok ot -> (Open, Ok(UnOp_T(op, ot)))
    | Error m -> (Open, Error m)
  )
  | ArraySize (refer) ->  (
    let (_, ty) = type_inner_reference refer env contexts in
    match ty with
    | Ok(T_Array _) -> (Open, Ok(NOp_T T_Int))
    | _ -> raise_failure "Array size of non-array value"
  )
  | GetInput ty -> (Open, Ok(NOp_T ty))
  | Bool _ -> (Open, Ok(NOp_T T_Bool))
  | Int _ -> (Open, Ok(NOp_T T_Int))
  | Char _ -> (Open, Ok(NOp_T T_Char))
  | NewArray (ty, _) -> (Open, Ok(NOp_T (T_Array(Some ty))))
  | ArrayLiteral elements -> ( match type_array_literal (List.map (fun e -> let (vm,ot) = type_expr e env contexts in if Result.is_ok ot then (vm,Ok (translate_operational_type (Result.get_ok ot))) else (vm,Error (Result.get_error ot))) elements) with 
    | (vmod, Ok ety) -> (vmod, Ok(NOp_T(T_Array(Some ety))))
    | (_, Error m) -> raise_failure m
  )
  | NewStruct (name, typ_args, args) -> ( match lookup_struct name env.var_env.structs with
    | Some (typ_vars, params) -> (
      if (List.length typ_vars > 0) then ( (* Generic *)
        let typ_args = resolve_type_args typ_vars typ_args (List.map (fun (a,b,_) -> (a,Some b)) params) args env contexts in
        (Open, Ok(NOp_T(T_Struct(name, typ_args))))
      )
      else (Open, Ok(NOp_T(T_Struct(name, typ_args)))) (* Not generic *)
    )
    | None -> raise_failure ("No such struct '" ^ name ^ "'")
  )
  | StructLiteral _ -> (Open, Error "Cannot type a struct literal") (*(Open, Ok(NOp_T(T_Struct("",[])))) This is causing issue*)
  | AnonRoutine (tv,args,_) -> (Open, Ok(NOp_T(T_Routine(tv, List.map (fun (a,b,_) -> (a,b)) args))))

  and replace_generic c typ_vars typ_args : (typ option, string) result = 
    let rec aux lst = 
      match lst with
      | [] -> Error "Could not resolve generic index"
      | (v,Some a)::t -> if v = c then Ok(Some a) else aux t
      | _::t -> aux t
    in
    Printf.printf "c: %c\n" c;
    List.iter (fun tv -> Printf.printf "tv: %c\n" tv) typ_vars ;
    List.iter (fun (ta) -> Printf.printf "ta: %s\n" ( Option.value ta ~default:T_Null |> type_string)) typ_args ;
    aux (try List.combine typ_vars typ_args with | _ -> raise_failure "Missing type args") 
  
  and replace_generics lst typ_vars typ_args : ((var_mod * typ option) list, string) result = 
    Printf.printf "Replaceing generics...\n" ;
    List.iter (fun e -> Printf.printf "pa: %s\n" (Option.value ~default:T_Null (snd e) |> type_string)) lst;
    List.iter (Printf.printf "tv: %c\n") typ_vars;
    List.iter (fun e -> Printf.printf "ta: %s\n" (Option.value ~default:T_Null e |> type_string)) typ_args;
    let rec replace element = 
      match element with
      | T_Generic(c) -> replace_generic c typ_vars typ_args
      | T_Array(sub) -> ( match replace (Option.get sub) with 
        | Ok t -> Ok(Some(T_Array t))
        | e -> e
      )
      | T_Struct(str_name, ta) -> (
        let rep = List.map (fun e -> replace (Option.get e)) ta in
        let rep' = (List.fold_left (fun acc e -> match acc, e with
          | Error m, _ -> Error m
          | _, Error m -> Error m
          | Ok rs, Ok r -> Ok (Some r::rs)
        ) (Ok []) rep) in match rep' with
        | Ok rs -> Ok(Some(T_Struct(str_name, rs |> List.map Option.join |> List.rev)))
        | Error m -> Error m
      )
      | T_Routine(_,ts) -> (
        let rep = ts |> List.map (fun (vm,t_opt) -> (vm, Option.get t_opt)) |> List.map (fun (vm,t) -> (vm, (replace t))) in
        let rep' = List.fold_left (fun acc e -> match acc, e with
          | Error m, _ -> Error m
          | _ , (_,Error m) -> Error m
          | Ok rs, (vm, Ok r) -> Ok ((vm,r)::rs)
        ) (Ok []) rep in match rep' with
        | Ok rs -> Ok(Some(T_Routine([],rs |> List.map (fun (vm,t) -> (vm, t)) |> List.rev)))
        | Error m -> Error m
      )
      | e -> Ok(Some(e))
    in
    let aux element =
      match element with
      | (vmod, Some ty) -> (vmod, replace ty)
      | (vmod, None) -> (vmod, Ok None)
    in
    let reps = List.map aux lst in
    match List.fold_left (fun acc e -> match acc, e with
      | Error m, _ -> Error m
      | _, (_,Error m) -> Error m
      | Ok rs, (v,Ok r) -> Ok ((v,Some r)::rs)
    ) (Ok []) reps with
    | Ok rs -> Ok (rs |> List.map (fun (vm, t_opt) -> (vm, Option.join t_opt)) |> List.rev)
    | Error msg -> Error msg
  
  (*and is_fully_defined_type typ_opt var_env =
    match typ_opt with
    | None -> false
    | Some(T_Array sub_t) -> is_fully_defined_type sub_t var_env
    | Some(T_Generic c) -> List.mem c var_env.typ_vars
    | Some(T_Struct(name, typ_args)) -> ( match lookup_struct name var_env.structs with
      | None -> false
      | Some(tvs,_) -> (List.length tvs = List.length typ_args) && List.fold_left (fun acc ta -> (is_fully_defined_type ta var_env) && acc) true typ_args 
    )
    | _ -> true*)

and well_defined_type typ_opt var_env =
  match typ_opt with
  | None -> false
  | Some(T_Array sub_t) -> well_defined_type sub_t var_env
  | Some(T_Generic c) -> List.mem c var_env.typ_vars
  | Some(T_Struct(name, typ_args)) -> ( match lookup_struct name var_env.structs with
    | None -> false
    | Some(tvs,_) -> (List.length tvs = List.length typ_args) && List.fold_left (fun acc ta -> (well_defined_type ta var_env) && acc) true typ_args 
  )
  | Some(T_Routine(_,ts)) -> List.fold_left (fun acc (_,t) -> well_defined_type t var_env && acc) true ts
  | _ -> true

  and dig_into_struct typ typ_vars_args_map param_arg_map var_env acc =
    match typ_vars_args_map with
    | [] -> acc
    | (c,Some(ta))::t when type_equal ta typ -> dig_into_struct typ t param_arg_map var_env (find_related_args (T_Generic c) param_arg_map var_env acc)
    | _::t -> dig_into_struct typ t param_arg_map var_env acc

  and find_related_args typ param_arg_map (env : environment) acc =
    match param_arg_map with
    | [] -> acc
    | ((_,None), _)::t -> find_related_args typ t env acc
    | ((_,Some p_typ), expr)::t when type_equal typ p_typ -> find_related_args typ t env (expr::acc)
    | ((_,Some T_Array(Some st)), Value(ArrayLiteral(exprs)))::t when type_equal st typ -> find_related_args typ t env (List.rev_append acc exprs)
    | (((_,Some T_Struct(name,typ_args)), expr)::t) -> find_related_args typ t env ( match lookup_struct name env.var_env.structs with
      | None -> raise_failure ("No such struct: " ^ name)
      | Some(tvs,params) -> ( match expr with
        | Value(StructLiteral(exprs)) -> dig_into_struct typ (List.combine tvs typ_args) (List.combine (List.map (fun (a,b,_) -> (a,Some b)) params) exprs) env acc
        | _ -> find_related_args typ t env acc
      )
    )
    | _::t -> find_related_args typ t env acc

  and is_generic t = 
    match t with
    | T_Generic _ -> true
    | _ -> false

  and find_possible_type typ param_arg_map (env : environment) contexts : (op_typ, string) result =
    match param_arg_map with
    | [] -> Error "Could not infere a type for unspecifed type argument"
    | ((_,None),_)::t -> find_possible_type typ t env contexts
    | ((_,Some p_typ), expr)::t when type_equal typ p_typ -> ( match type_expr expr env contexts with 
      | (_,Ok ot) -> Ok ot
      | _ -> find_possible_type typ t env contexts
    )
    | ((_,Some T_Array(Some st)), expr)::t when type_equal st typ -> ( match type_expr expr env contexts with
      | (_,Ok ot) -> ( match translate_operational_type ot with
        | T_Array(Some st) -> Ok(NOp_T st)
        | _ -> find_possible_type typ t env contexts
      )
      | _ -> find_possible_type typ t env contexts
    )
    | (((_,Some T_Routine(_,params)), expr)::t) -> ( match type_expr expr env contexts with
      | (_,Ok ot) -> ( match translate_operational_type ot with
        | T_Routine(_,ps) -> ( 
          if not(List.length ps = List.length params) 
            then find_possible_type typ t env contexts 
            else match List.fold_left (fun acc ((_,p1),(_,p2)) -> if Result.is_ok acc then acc else (if Option.is_some p1 && type_equal typ (Option.get p1) then (if Option.is_some p2 && not(is_generic (Option.get p2)) then (Ok (Option.get p2)) else acc) else acc) ) (Error "Sad") (List.combine params ps) with
            | Ok t -> Ok(NOp_T t)
            | _ -> find_possible_type typ t env contexts
        )
        | _ -> find_possible_type typ t env contexts
      )
      | _ -> find_possible_type typ t env contexts
    )
    | (((_,Some T_Struct(name,_)), expr)::t) -> ( match lookup_struct name env.var_env.structs with
      | None -> raise_failure ("No such struct: " ^ name)
      | Some(_,params) -> ( match expr with
        | Value(StructLiteral(exprs)) -> (
          find_possible_type typ (List.combine (List.map (fun (a,b,_) -> (a,Some b)) params) exprs) env contexts
        )
        | _ -> find_possible_type typ t env contexts
      )
    )
    | _::t -> find_possible_type typ t env contexts

  and get_first_type exprs env contexts =
    match exprs with
    | [] -> Error "Could not infer type from context"
    | h::t -> try (
      let (_,typ_res) = type_expr h env contexts in
      match typ_res with
      | Error m -> Error m
      | Ok ot -> if (translate_operational_type ot) = T_Null then get_first_type t env contexts else typ_res
    ) with | _ -> get_first_type t env contexts

  and fix_type_args typ_vars typ_args =
    if typ_args = [] then List.init (List.length typ_vars) (fun _ -> None)
    else if List.length typ_args = List.length typ_vars then typ_args
    else raise_failure ("Expected " ^(string_of_int (List.length typ_vars))^ " type arguments, but was given " ^(string_of_int (List.length typ_args))) 

  and resolve_type_args typ_vars typ_args (params : (var_mod * typ option) list) args (env : environment) contexts =
    let typ_args = fix_type_args typ_vars typ_args in
    let rec aux tvas acc =
      match tvas with
      | [] -> List.rev acc
      | (c,typ_arg)::t -> ( match well_defined_type typ_arg env.var_env with
        | true -> aux t (typ_arg::acc)
        | false -> ( match typ_arg with
          | None -> ( match find_possible_type (T_Generic c) (List.combine params args) env contexts with (*match get_first_type (find_related_args (T_Generic c) (List.combine params args) env []) env contexts with*)
            | Ok ot -> aux t (Some(translate_operational_type ot)::acc)
            | Error _ -> aux t (None::acc)
          )
          | Some(T_Struct(name,tas)) -> ( match lookup_struct name env.var_env.structs with
            | None -> raise_failure ("No such struct: " ^ name)
            | Some(tvs,ps) -> (
              let rec infer_from_related related_exprs =
                match related_exprs with
                | [] -> raise_failure "Could not infer a type from context"
                | Value(StructLiteral(exprs))::t -> (try (Some(T_Struct(name, resolve_type_args tvs tas (List.map (fun (a,b,_) -> (a,Some b)) ps) exprs env contexts))) with | _ -> infer_from_related t)
                | Value(NewStruct(name,tas,exprs))::t -> ( match lookup_struct name env.var_env.structs with
                  | Some(tvs,ps) -> (try (Some(T_Struct(name, resolve_type_args tvs tas (List.map (fun (a,b,_) -> (a, Some b)) ps) exprs env contexts))) with | _ -> infer_from_related t)
                  | None -> raise_failure ("No such struct: " ^ name)
                )
                | Reference(Null)::t -> infer_from_related t
                | _::t -> infer_from_related t
              in
              aux t ((infer_from_related (find_related_args (T_Generic(c)) (List.combine params args) env []))::acc)
            )
          )
          | _ -> raise_failure "This should not happen 1"
        )
      )
    in
    aux (List.combine typ_vars typ_args) []

let rec fillout_missing_type t_opt expr = match t_opt, expr with
  | Some T_Routine(_,p_params), Value AnonRoutine(generics,a_params,body) -> Value(AnonRoutine(generics, List.map ( fun (p_param,a_param) -> match p_param,a_param with
    | (_,None),(_,None,_) -> raise_failure ("Nothing to fill out with")
    | (_,Some t),(a_vm,None,n) -> (a_vm, Some t, n)
    | _,(a_vm,Some t,n) -> (a_vm, Some t, n)) (List.combine p_params a_params), body
  ))
  | Some T_Array(st_opt), Value ArrayLiteral(exprs) -> Value(ArrayLiteral(List.map (fun expr -> fillout_missing_type st_opt expr) exprs))
  | _,_ -> expr

let fillout_untyped_routine_parameters params args = 
  List.combine params args |> List.map (fun (p,a) -> fillout_missing_type p a)

let elements_unique lst =
  let rec aux l seen =
    match l with
    | [] -> true
    | h::t -> if List.mem h seen then false else aux t (h::seen)
  in
  aux lst []

let parameters_check typ_vars structs params =
  let rec check p_ty =
    match p_ty with
    | T_Int
    | T_Bool
    | T_Char -> true
    | T_Null -> false
    | T_Array(sub_ty) -> check (Option.get sub_ty)
    | T_Generic(c) -> if List.mem c typ_vars then true else false
    | T_Struct(name, typ_args) -> ( match lookup_struct name structs with
      | Some(tvs, _) -> List.length tvs = List.length typ_args && List.fold_left (fun acc field_ty -> (check (Option.get field_ty)) && acc) true typ_args
      | None -> false
    )
    | T_Routine(_,types) -> List.fold_left (fun acc (_,typ) -> (check (Option.get typ)) && acc) true types
  in
  List.fold_left (fun acc ty -> (check ty) && acc) true params

let check_topdecs file structs =
  let rec aux tds =
    match tds with
    | [] -> ()
    | GlobalDeclaration(Entry,dec)::t -> ( match dec with
      | TypeDeclaration(_,T_Routine(_,ps),_) -> ( match List.for_all (fun (_,pt) -> simple_type (Option.get pt)) ps with
        | true -> aux t
        | false -> raise_failure "Entry points can only have simple types as parameters"
      )
      | TypeDeclaration(_,_,_) -> raise_failure "Entry points must be a routine"
      | AssignDeclaration(_,Some(T_Routine(_,ps)),_,_) -> ( match List.for_all (fun (_,pt) -> simple_type (Option.get pt)) ps with
        | true -> aux t
        | false -> raise_failure "Entry points can only have simple types as parameters"
      )
      | AssignDeclaration(_,None,_,Value(AnonRoutine(_,nps,_))) -> ( match List.for_all (fun (_,pt,_) -> simple_type (Option.get pt)) nps with
        | true -> aux t
        | false -> raise_failure "Entry points can only have simple types as parameters"
      )
      | AssignDeclaration(_,_,_,_) -> raise_failure  "Entry points must be a routine"
    )
    | GlobalDeclaration(_,dec)::t -> ( match dec with
      | TypeDeclaration(_,T_Routine(typ_vars,params),name) -> ( 
        if not(elements_unique typ_vars) then raise_failure ("Non-unique type variables in routine definition '" ^ name ^ "'")
        else if List.exists (fun (_,t_opt) -> Option.is_none t_opt) params then raise_failure ("Cannot have untyped parameters in type definition of routine '" ^ name ^ "'")
        else if not(parameters_check typ_vars structs (List.map (fun (_,t_opt) -> Option.get t_opt) params)) then raise_failure ("illegal parameters in defenition of routine '" ^ name ^ "'")
        else aux t
      )
      | AssignDeclaration(_,Some(T_Routine(typ_vars,params)),name,_) -> ( 
        if not(elements_unique typ_vars) then raise_failure ("Non-unique type variables in routine definition '" ^ name ^ "'")
        else if not(parameters_check typ_vars structs (List.map (fun (_,t_opt) -> Option.get t_opt) params)) then raise_failure ("illegal parameters in defenition of routine '" ^ name ^ "'")
        else aux t
      )
      | AssignDeclaration(_,None,name,Value(AnonRoutine(typ_vars,nps,_))) -> (
        if not(elements_unique typ_vars) then raise_failure ("Non-unique type variables in routine definition '" ^ name ^ "'")
        else if not(parameters_check typ_vars structs (List.map (fun (_,b,_) -> Option.get b) nps)) then raise_failure ("illegal parameters in defenition of routine '" ^ name ^ "'")
        else aux t
      )
      | _ -> aux t
    )
    | Struct(name,typ_vars,params)::t -> ( 
      if not(elements_unique typ_vars) then raise_failure ("Non-unique type variables in struct definition '" ^ name ^ "'")
      else if not(parameters_check typ_vars structs (List.map (fun (_,b,_) -> b) params)) then raise_failure ("illegal parameters in defenition of struct '" ^ name ^ "'")
      else aux t
    )
    | _::t -> aux t
  in
  match file with
  | File(tds) -> aux tds

let check_structs structs =
  StringMap.fold (fun name _ seen -> 
    if StringSet.mem name seen then raise_failure ("Duplicate struct name '" ^ name ^ "'") else (StringSet.add name seen)
  ) structs StringSet.empty |> ignore

let check_struct_literal struct_fields expr (env : environment) contexts =
  let rec aux (pairs : ((var_mod * typ option) * expression) list) =
    match pairs with
    | [] -> true 
    | ((_,Some T_Struct(name,typ_args)), Value(StructLiteral(exprs)))::t -> (
      match lookup_struct name env.var_env.structs with
      | None -> false
      | Some(tvs,ps) -> (
        match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) ps) tvs typ_args with
        | Ok rs -> aux (List.combine rs exprs)
        | Error m -> raise_failure (m ^ "big sad")
      ) && aux t
    )
    | ((_,Some T_Null),_)::_ -> false
    | ((vmod,Some typ),e)::t -> (
      let (expr_vmod, expr_typ_res) = type_expr e env contexts in
      match expr_typ_res with
      | Ok(expr_typ) -> (
        if not(type_equal typ (translate_operational_type expr_typ)) then false else
        if vmod = Open && (expr_vmod = Stable || expr_vmod = Const) then false else
        aux t
      )
      | Error _ -> false
    )
    | ((_, None),_)::_ -> raise_failure "Missing struct field type"
  in match expr with
  | Value(StructLiteral(exprs)) -> (try aux (List.combine struct_fields exprs) with | _ -> false)
  | Reference(Null) -> true
  | _ -> false

let match_typ_arg ts =
  match ts with
  | None, Some t -> Some t
  | Some t, None -> Some t
  | Some(t1), Some(t2) when type_equal t1 t2 -> Some t1
  | _ -> raise_failure "Type match failed" 

let resolve_type typ_opt expr (env : environment) contexts : typ =
  match typ_opt with
  | Some(typ) -> ( match typ with
    | T_Generic c -> raise_failure ((String.make 1 c) ^ " is not defined in this scope")
    | T_Array(_) -> raise_failure "not implemented"
    | T_Struct(name,typ_args) -> (match lookup_struct name env.var_env.structs with
      | None -> raise_failure ("No such struct: " ^ name)
      | Some(typ_vars,params) -> ( match expr with
        | Reference(Null) -> raise_failure "Cannot infer from null"
        | Reference(ref) -> (Result.get_ok (snd(type_reference ref env contexts)))
        | Value(StructLiteral(exprs)) -> (
            let typ_args = resolve_type_args typ_vars typ_args (List.map (fun (a,b,_) -> (a,Some b)) params) exprs env contexts in
            match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) params) typ_vars typ_args with
            | Ok params -> (
              if not(check_struct_literal params (Value (StructLiteral exprs)) env contexts) then raise_failure ("Could not match struct literal with '" ^ type_string (T_Struct(name,typ_args)) ^ "'")
              else (T_Struct(name,typ_args))
            )
            | Error m -> raise_failure (m^"wtf man")
        )
        | Value(NewStruct(expr_name,tas,args)) -> (
            if not(expr_name = name) then raise_failure "mismatched struct names" else
            let expr_typ_args = resolve_type_args typ_vars tas (List.map (fun (a,b,_) -> (a,Some b)) params) args env contexts in
            let typ_args = List.map (fun x -> (fst x)) (List.combine typ_args expr_typ_args) in
            (T_Struct(name,typ_args))
        )
        | _ -> raise_failure "cannot infer"
      )
    )
    | _ -> raise_failure "well-definedness checker has failed"
  )
  | None -> let (_, t) = type_expr expr env contexts in translate_operational_type (Result.get_ok t)

let declaration_checks target_vmod target_typ expr_vmod expr_typ =
    if target_vmod = Open && expr_vmod != Open then raise_failure "Cannot assign a protected variable to an open variable"
    else if not (type_equal target_typ (translate_operational_type expr_typ)) then raise_failure ("Type mismatch: expected '" ^ (type_string target_typ) ^ "', got '" ^ (type_string (translate_operational_type expr_typ)) ^ "'")
    else match expr_typ with
      | NOp_T(T_Null) -> Ok (NOp_T target_typ)
      | _ -> Ok expr_typ

let argument_checks target_vmod target_typ expr_vmod expr_typ =
    if target_vmod = Open && (expr_vmod != Open) then raise_failure "Cannot use a protected variable as an open variable"
    else if target_vmod = Stable && (expr_vmod = Const) then raise_failure "Cannot use a constant variable as a stable parameter"
    else if not (type_equal target_typ (translate_operational_type expr_typ)) then raise_failure ("Type mismatch: expected '" ^ (type_string target_typ) ^ "', got '" ^ (type_string (translate_operational_type expr_typ)) ^ "'")
    else match expr_typ with
      | NOp_T(T_Null) -> Ok (NOp_T target_typ)
      | _ -> Ok expr_typ

let rec type_check checks vmod typ expr (env : environment) contexts : (op_typ, string) result =
  Printf.printf "Type checking...\n";
  match typ, expr with
  | None, Value(StructLiteral(_)) -> Error "Cannot infer a type from a struct literal"
  | Some(T_Struct _ as t), Reference(Null) -> if well_defined_type (Some t) env.var_env then Ok (NOp_T t) else Error "Cannot infer a type from 'null'"
  | None, Value(ArrayLiteral elems) -> (
    let elem_types = List.map (fun elem -> type_check checks vmod None elem env contexts) elems in
    let t = List.fold_left (fun acc t -> match acc with
      | Error _ -> if t = Ok(NOp_T T_Null) then Error "Only nulls in array literal" else t
      | Ok(a) -> if Result.is_error t then acc else if type_equal (translate_operational_type a) (translate_operational_type(Result.get_ok t)) then acc else Error ("Array literal contains unequatable types")
    ) (Error "Cannot infer a type from the empty array") elem_types in
    if Result.is_ok t then type_check checks vmod (Some(T_Array(Some(translate_operational_type(Result.get_ok t))))) expr env contexts else t
  )
  | Some(T_Array(Some st)), Value(ArrayLiteral []) -> if well_defined_type (Some st) env.var_env then Ok(NOp_T(T_Array(Some(st)))) else Error "Not a well defined type"
  | Some(T_Array(Some(T_Routine(tv,rst)))), Value(ArrayLiteral elems) -> (
    let ress = List.map (fun elem -> type_check checks vmod (Some(T_Routine(tv,rst))) elem env contexts) elems in
    List.fold_left (fun acc res -> if Result.is_error acc then acc else if Result.is_error res then res else acc) (Ok(NOp_T(T_Array(Some(T_Routine(tv,rst)))))) ress
  )
  | Some(T_Array(Some st)), Value(ArrayLiteral elems) -> (
    let elem_types = List.map (fun elem -> type_check checks vmod (Some st) elem env contexts) elems in
    let t = List.fold_left (fun acc t -> match acc with
      | Error _ -> if t = Ok(NOp_T T_Null) then acc else t
      | Ok t -> Ok t
    ) (Error "Could not find a well-defined type in array") elem_types in
    match t with
    | Ok st -> (
      let ress = List.map (fun elem -> type_check checks vmod (Some (translate_operational_type st)) elem env contexts) elems in
      let t = List.fold_left (fun acc t -> match acc with
        | Ok a -> (match t with
          | Ok b -> if type_equal (translate_operational_type a) (translate_operational_type b) then Ok b else Error ("Array literal contains unequatable types")
          | e -> e
        )
        | e -> e
      ) (Ok(NOp_T T_Null)) ress in match t with
      | Ok t -> Ok(NOp_T(T_Array(Some (translate_operational_type t))))
      | e -> e
    )
    | e -> e
  )
  | Some(T_Struct(_,_)), (Ternary(cond,exp1,exp2)) -> (
    let (_,cond_typ_res) = type_expr cond env contexts in
    match cond_typ_res with
    | Error _ as e -> e
    | Ok(op_typ) -> ( match translate_operational_type op_typ with
      | T_Bool -> (
        match type_check checks vmod typ exp1 env contexts, type_check checks vmod typ exp2 env contexts with
        | Ok(ot1), Ok(ot2) -> if type_equal (translate_operational_type ot1) (translate_operational_type ot2) then Ok(TernaryOp_T(op_typ,ot1,ot2)) else failwith "Not same type ternary"
        | _ -> failwith "Ternary had differing types"
      )
      | _ -> raise_failure "Condition of ternary was not a bool"
    )
  )
  | Some(T_Struct(name,typ_args)), (Value(StructLiteral(exprs)) as literal) -> ( match lookup_struct name env.var_env.structs with
    | Some(typ_vars,params) ->  (
      let typ_args = if typ_args = [] then List.init (List.length typ_vars) (fun _ -> None) else typ_args in
      let typ_args = resolve_type_args typ_vars typ_args (List.map (fun (a,b,_) -> (a,Some b)) params) exprs env contexts in
      match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) params) typ_vars typ_args with
      | Error _ as e -> e
      | Ok params -> (
        if not(check_struct_literal params literal env contexts) then Error ("Could not match struct literal with '" ^ type_string (T_Struct(name,typ_args)) ^ "'")
        else Ok(NOp_T(T_Struct(name,typ_args)))
      )
    )
    | None -> raise_failure ("No such struct '" ^ name ^ "'")
  )
  | Some(T_Struct(name,typ_args)), Value(NewStruct(expr_name,tas,args)) -> ( match lookup_struct name env.var_env.structs with
    | Some(typ_vars,params) ->  (
      if not(expr_name = name) then raise_failure "mismatched struct names" else
      let matched_typ_args = List.map (fun ts -> match_typ_arg ts) (List.combine (fix_type_args typ_vars typ_args) (fix_type_args typ_vars tas)) in
      let resolved_typ_args = resolve_type_args typ_vars matched_typ_args (List.map (fun (a,b,_) -> (a,Some b)) params) args env contexts in
      match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) params) typ_vars resolved_typ_args with
      | Ok params -> (
        if not(List.fold_left (fun acc ((_,param_typ_opt),arg) -> acc && type_equal (Option.get param_typ_opt) (translate_operational_type(Result.get_ok (snd(type_expr arg env contexts))))) true (List.combine params args)) then raise_failure ("Struct argument type mismatch") 
        else Ok(NOp_T(T_Struct(name,resolved_typ_args)))
      )
      | Error m -> raise_failure (m^"lol what")
    )
    | None -> raise_failure ("No such struct '" ^ name ^ "'")
  )
  | None, Value(NewStruct(name,typ_args,args)) -> ( match lookup_struct name env.var_env.structs with
    | Some(typ_vars,params) ->  (
      let resolved_typ_args = resolve_type_args typ_vars typ_args (List.map (fun (a,b,_) -> (a,Some b)) params) args env contexts in
      match replace_generics (List.map (fun (a,b,_) -> (a,Some b)) params) typ_vars resolved_typ_args with
      | Ok params -> (
        if not(List.fold_left (fun acc ((_,param_typ_opt),arg) -> acc && type_equal (Option.get param_typ_opt) (translate_operational_type(Result.get_ok (snd(type_expr arg env contexts))))) true (List.combine params args)) then raise_failure ("Struct argument type mismatch") 
        else Ok(NOp_T(T_Struct(name,resolved_typ_args)))
      )
      | Error m -> raise_failure (m^"more fails")
    )
    | None -> raise_failure ("No such struct '" ^ name ^ "'")
  )
  | None, expr -> (
    let (vm,res) = type_expr expr env contexts in 
    match res with
    | Ok(expr_typ) -> checks vmod (translate_operational_type expr_typ) vm expr_typ
    | Error m -> Error m
  )
  | Some(target_typ), expr -> (
    Printf.printf "aaa\n";
    let (vm, typ_res) = type_expr expr env contexts in
    match typ_res with
    | Ok(expr_typ) -> checks vmod target_typ vm expr_typ
    | Error m -> Error m
  )


let argument_type_check = type_check argument_checks
let declaration_type_check = type_check declaration_checks

let assignment_checks expr target_vmod target_typ expr_vmod expr_typ =
  if not(type_equal target_typ (translate_operational_type expr_typ)) then raise_failure ("Type mismatch in assignment: "^type_string target_typ^" := "^ type_string (translate_operational_type expr_typ))
  else match target_vmod with
  | Open -> (
    if expr_vmod != Open then raise_failure "Assignment of protected variable, to non-protected variable"
    else Ok expr_typ
  )
  | Stable -> ( match expr with
    | Value _ -> raise_failure "Attempt to overwrite stable data"
    | Reference _ -> Ok expr_typ
    | Ternary _ -> Ok expr_typ
  )
  | Const -> raise_failure "Assignment to a protected variable"

let assignment_type_check (target: reference) (assign: expression) (env: environment) (contexts: context list): (op_typ,string) result =
  let (vm,typ_res) = type_reference target env contexts in
  match typ_res with
  | Ok t -> type_check (assignment_checks assign) vm (Some t) assign env contexts
  | Error m -> Error m