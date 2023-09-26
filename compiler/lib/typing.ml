open ProgramRep
open Exceptions
open Absyn
open Helpers

let rec type_string t =
  match t with
  | T_Bool -> "bool"
  | T_Int -> "int"
  | T_Char -> "char"
  | T_Array arr_ty -> (type_string (Option.get arr_ty))^"[]"
  | T_Struct(n,typ_args) -> n ^ "<" ^ (String.concat ","  (List.map (fun e -> (type_string (Option.get e))) typ_args)) ^ ">"
  | T_Null -> "null"
  | T_Generic c -> String.make 1 c

let rec type_equal type1 type2 =
  let aux t1 t2 =
    match (t1, t2) with
    | (T_Int, T_Int) -> true
    | (T_Bool, T_Bool) -> true
    | (T_Char, T_Char) -> true
    | (T_Array at1, T_Array at2) -> type_equal (Option.get at1) (Option.get at2)
    | (T_Struct(n1,ta1), T_Struct(n2, ta2)) when n1 = n2 && (List.length ta1) = (List.length ta2) -> true && (List.fold_right (fun e acc -> (type_equal (Option.get (fst e)) (Option.get (snd e))) && acc) (List.combine ta1 ta2) true)
    | (T_Null, _) -> true
    | (T_Generic c1, T_Generic c2) -> c1 = c2
    | _ -> false
  in aux type1 type2 || aux type2 type1

let type_array_literal lst =
  let rec aux_type ty vmod li =
    match li with
    | [] -> (vmod,ty)
    | (expr_vmod,h)::t -> (
      if not (type_equal h ty) then raise_error "Array literal containing expressions of differing types"
      else aux_type ty (strictest_mod vmod expr_vmod) t
    )
  in
  match lst with 
  | [] -> (Open, T_Null)
  | (vmod,h)::t -> aux_type h vmod t

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
  
let rec type_expr expr var_env =
  match expr with
  | Reference ref_expr -> type_reference ref_expr var_env
  | Value val_expr -> type_value val_expr var_env

and type_reference ref_expr var_env =
  match ref_expr with
  | VariableAccess name -> (var_modifier name var_env, var_type name var_env)
  | StructAccess (refer, field) -> (
    let (vmod, ty) =  type_reference refer var_env in
    match ty with 
    | T_Struct (str_name, typ_args) -> (match lookup_struct str_name var_env.structs with
      | Some (typ_vars, fields) -> (
        let resolved_fields = replace_generics fields typ_vars typ_args in
        let (field_mod, field_ty,_) = struct_field field resolved_fields in
        ((if vmod = Open then field_mod else Const), field_ty)
      )
      | None -> raise_error ("No such struct '" ^ str_name ^ "'")
    )
    | _ -> raise_error ("Field access of non-struct value")
  )
  | ArrayAccess (refer, _) -> (
    let (vmod, ty) =  type_reference refer var_env in
    match ty with 
    | T_Array array_typ -> (vmod, Option.get array_typ)
    | _ -> raise_error ("Array access of non-array value")
  )
  | Null -> (Open, T_Null)

and type_value val_expr var_env =
  match val_expr with
  | Binary_op (op, expr1, expr2) -> (
    let (_, ty1) = type_expr expr1 var_env in
    let (_, ty2) = type_expr expr2 var_env in
    match (op, ty1, ty2) with
    | ("&&", T_Bool, T_Bool) ->  (Open, T_Bool)
    | ("||", T_Bool, T_Bool) -> (Open, T_Bool)
    | ("=", _, T_Null) -> (Open, T_Bool)
    | ("=", T_Null, _) -> (Open, T_Bool)
    | ("=", T_Bool, T_Bool) -> (Open, T_Bool)
    | ("=", T_Char, T_Char) -> (Open, T_Bool)
    | ("=", T_Int, T_Int) -> (Open, T_Bool)
    | ("!=", _, T_Null) -> (Open, T_Bool)
    | ("!=", T_Null, _) -> (Open, T_Bool)
    | ("!=", T_Bool, T_Bool) -> (Open, T_Bool)
    | ("!=", T_Char, T_Char) -> (Open, T_Bool)
    | ("!=", T_Int, T_Int) -> (Open, T_Bool)
    | ("<=", T_Int, T_Int) -> (Open, T_Bool) 
    | ("<", T_Int, T_Int) -> (Open, T_Bool)
    | (">=", T_Int, T_Int) -> (Open, T_Bool)
    | (">", T_Int, T_Int) -> (Open, T_Bool)
    | ("+", T_Int, T_Int) -> (Open, T_Int)
    | ("-", T_Int, T_Int) -> (Open, T_Int)
    | ("*", T_Int, T_Int) -> (Open, T_Int)
    | _ -> raise_error "Unknown binary operator, or type mismatch"
  )
  | Unary_op (op, expr) -> (
    let (_, ty) = type_expr expr var_env in
    match (op, ty) with
    | ("!", T_Bool) -> (Open, T_Bool)
    | _ -> raise_error "Unknown unary operator, or type mismatch"
  )
  | ArraySize (refer) ->  (
    let (_, ty) = type_reference refer var_env in
    match ty with
    | T_Array _ -> (Open, T_Int)
    | _ -> raise_error "Array size of non-array value"
  )
  | GetInput ty -> (Open, ty)
  | Bool _ -> (Open, T_Bool)
  | Int _ -> (Open, T_Int)
  | Char _ -> (Open, T_Char)
  | ValueOf (refer) -> type_reference refer var_env
  | NewArray (ty, _) -> (Open, T_Array(Some ty))
  | ArrayLiteral elements -> (match type_array_literal (List.map (fun e -> type_expr e var_env) elements) with (vmod,ety) -> (vmod, T_Array(Some ety)))
  | NewStruct (name, typ_args, args) -> ( match lookup_struct name var_env.structs with
    | Some (typ_vars, params) -> (
      if (List.length typ_vars > 0) then ( (* Generic *)
        let typ_args = resolve_type_args typ_vars typ_args params args var_env in
        (Open, T_Struct(name, typ_args))
      )
      else (Open, T_Struct(name, typ_args)) (* Not generic *)
    )
    | None -> raise_error ("No such struct '" ^ name ^ "'")
  )
  | StructLiteral _ -> raise_error "Cannot infere a type from a struct literal"

  and replace_generic c typ_vars typ_args = 
    let rec aux lst = 
      match lst with
      | [] -> failwith "Could not resolve generic index"
      | (v,a)::t -> if v = c then a else aux t
    in
    aux (try List.combine typ_vars typ_args with | _ -> raise_error "meme") 
  
  and replace_generics lst typ_vars typ_args = 
    let rec replace element = 
      match element with
      | T_Generic(c) -> replace_generic c typ_vars typ_args
      | T_Array(sub) -> Some (T_Array((replace (Option.get sub))))
      | T_Struct(str_name, ta) -> Some (T_Struct(str_name, List.map (fun e -> replace (Option.get e)) ta))
      | e -> Some e
    in
    let aux element =
      match element with
      | (vmod, ty, name) -> (vmod, replace ty, name)
    in
    List.map (fun e -> match aux e with (a,t,b) -> (a,Option.get t,b)) lst
  
  and is_fully_defined_type typ_opt var_env =
    match typ_opt with
    | None -> false
    | Some(T_Array sub_t) -> is_fully_defined_type sub_t var_env
    | Some(T_Generic c) -> List.mem c var_env.typ_vars
    | Some(T_Struct(name, typ_args)) -> ( match lookup_struct name var_env.structs with
      | None -> false
      | Some(tvs,_) -> (List.length tvs = List.length typ_args) && List.fold_left (fun acc ta -> (is_fully_defined_type ta var_env) && acc) true typ_args 
    )
    | _ -> true

  and dig_into_struct typ typ_vars_args_map param_arg_map var_env acc =
    match typ_vars_args_map with
    | [] -> acc
    | (c,Some(ta))::t when type_equal ta typ -> dig_into_struct typ t param_arg_map var_env (find_related_args (T_Generic c) param_arg_map var_env acc)
    | _::t -> dig_into_struct typ t param_arg_map var_env acc

  and find_related_args typ param_arg_map var_env acc =
    match param_arg_map with
    | [] -> acc
    | ((_,p_typ,_), expr)::t when type_equal typ p_typ -> find_related_args typ t var_env (expr::acc)
    | (((_,T_Struct(name,typ_args),_), expr)::t) -> find_related_args typ t var_env ( match lookup_struct name var_env.structs with
      | None -> raise_error ("No such struct: " ^ name)
      | Some(tvs,params) -> ( match expr with
        | Value(StructLiteral(exprs)) -> dig_into_struct typ (List.combine tvs typ_args) (List.combine params exprs) var_env acc
        | _ -> find_related_args typ t var_env acc
      )
    )
    | _::t -> find_related_args typ t var_env acc

  and get_first_type exprs var_env =
    match exprs with
    | [] -> raise_error "Could not infer type from context"
    | h::t -> try (
      let (_,typ) = type_expr h var_env in
      if typ = T_Null then get_first_type t var_env else typ
    ) with | _ -> get_first_type t var_env

  and resolve_type_args typ_vars typ_args params args var_env =
    let typ_args = 
      if typ_args = [] then List.init (List.length typ_vars) (fun _ -> None)
      else if List.length typ_args = List.length typ_vars then typ_args
      else raise_error ("Expected " ^(string_of_int (List.length typ_vars))^ " type arguments, but was given " ^(string_of_int (List.length typ_args))) 
    in
    let rec aux tvas acc =
      match tvas with
      | [] -> List.rev acc
      | (c,typ_arg)::t -> ( match is_fully_defined_type typ_arg var_env with
        | true -> aux t (typ_arg::acc)
        | false -> ( match typ_arg with
          | None -> aux t (Some(get_first_type (find_related_args (T_Generic c) (List.combine params args) var_env []) var_env)::acc)
          | Some(T_Struct(name,tas)) -> ( match lookup_struct name var_env.structs with
            | None -> raise_error ("No such struct: " ^ name)
            | Some(tvs,ps) -> (
              let rec infer_from_related related_exprs =
                match related_exprs with
                | [] -> raise_error "Could not infer a type from context"
                | Value(StructLiteral(exprs))::t -> (try (Some(T_Struct(name, resolve_type_args tvs tas ps exprs var_env))) with | _ -> infer_from_related t)
                | Value(NewStruct(name,tas,exprs))::t -> ( match lookup_struct name var_env.structs with
                  | Some(tvs,ps) -> (try (Some(T_Struct(name, resolve_type_args tvs tas ps exprs var_env))) with | _ -> infer_from_related t)
                  | None -> raise_error ("No such struct: " ^ name)
                )
                | Reference(Null)::t -> infer_from_related t
                | _::t -> infer_from_related t
              in
              aux t ((infer_from_related (find_related_args (T_Generic(c)) (List.combine params args) var_env []))::acc)
            )
          )
          | _ -> raise_error "This should not happen 1"
        )
      )
    in
    aux (List.combine typ_vars typ_args) []

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
      | Some(tvs, _) -> List.length tvs = List.length typ_args && List.fold_right (fun field_ty acc -> (check (Option.get field_ty)) && acc) typ_args true
      | None -> false
    )
  in
  List.fold_right (fun (_,ty,_) acc -> (check ty) && acc) params true

let rec well_defined_type typ var_env =
  match typ with
  | T_Struct(name,typ_args) -> (
    match lookup_struct name var_env.structs with
    | None -> false
    | Some(typ_vars,_) -> (List.length typ_args == List.length typ_vars) && (List.fold_right (fun e acc -> (well_defined_type (Option.get e) var_env) && acc ) typ_args true)
  )
  | T_Array sub -> well_defined_type (Option.get sub) var_env
  | T_Generic c -> List.mem c var_env.typ_vars
  | _ -> true

let check_topdecs file structs =
  let rec aux tds =
    match tds with
    | [] -> ()
    | Routine(_,name,typ_vars,params,_)::t -> (
      if not(elements_unique typ_vars) then raise_error ("Non-unique type variables in routine definition '" ^ name ^ "'")
      else if not(parameters_check typ_vars structs params) then raise_error ("illegal parameters in defenition of routine '" ^ name ^ "'")
      else aux t
    )
    | Struct(name,typ_vars,params)::t -> ( 
      if not(elements_unique typ_vars) then raise_error ("Non-unique type variables in struct definition '" ^ name ^ "'")
      else if not(parameters_check typ_vars structs params) then raise_error ("illegal parameters in defenition of struct '" ^ name ^ "'")
      else aux t
    )
    | _::t -> aux t
  in
  match file with
  | File(tds) -> aux tds

let check_structs structs =
  let rec aux strs seen =
    match strs with
    | [] -> ()
    | (name, _, _)::t -> if List.mem name seen then raise_error ("Duplicate struct name '" ^ name ^ "'") else aux t (name::seen) 
  in
  aux structs []

let rec check_struct_literal struct_fields expr var_env =
  let rec aux pairs =
    match pairs with
    | [] -> true 
    | ((_,T_Struct(name,typ_args),_),expr)::_ -> (
      match lookup_struct name var_env.structs with
      | None -> false
      | Some(tvs,ps) -> (
        let replaced = replace_generics ps tvs typ_args in
        check_struct_literal replaced expr var_env
      )
    )
    | ((_,T_Null,_),_)::_ -> false
    | ((vmod,typ,_),e)::t -> (
      let (expr_vmod, expr_typ) = type_expr e var_env in
      if not(type_equal typ expr_typ) then false else
      if vmod = Open && (expr_vmod = Stable || expr_vmod = Const) then false else
      aux t
    )
  in match expr with
  | Value(StructLiteral(exprs)) -> (try aux (List.combine struct_fields exprs) with | _ -> false)
  | Reference(Null) -> true
  | _ -> false

let assignment_type_check target assign var_env =
  let (target_vmod, target_type) = type_reference target var_env in
  let (assign_vmod, assign_type) = match assign with
  | Value(StructLiteral(exprs)) -> ( match target_type with
    | T_Struct(name, typ_args) -> ( match lookup_struct name var_env.structs with
      | Some(typ_vars, params) -> (
        let typ_args = resolve_type_args typ_vars typ_args params exprs var_env in
        if not(check_struct_literal (replace_generics params typ_vars typ_args) (Value(StructLiteral exprs)) var_env) then raise_error "Structure mismatch in assignment"
        else (Open, T_Struct(name, typ_args))
      )
      | None -> raise_error ("No such struct '" ^ name ^ "'")
    )
    | _ -> raise_error ("Struct literal assignment to a variable of type '" ^ type_string target_type ^ "'")
  )
  | _ -> (
    let (assign_vmod, assign_type) = type_expr assign var_env in
    if not (type_equal target_type assign_type) then raise_error ("Type mismatch in assignment, expected '"^(type_string target_type)^"' but got '" ^(type_string assign_type)^ "'") 
    else (assign_vmod, assign_type)
  )
  in
  match target_vmod with
  | Open -> (
    if assign_vmod != Open then raise_error "Assignment of protected variable, to non-protected variable"
    else assign_type
  )
  | Stable -> ( match assign with
    | Value _ -> raise_error "Attempt to overwrite stable data"
    | Reference _ -> assign_type
  )
  | Const -> raise_error "Assignment to a protected variable"

let rec meme typ_vars typ_args params array_exprs var_env =
  match array_exprs with
  | [] -> raise_error "Fuck dig"
  | Value(StructLiteral(exprs))::t -> ( try (
    let typ_args = resolve_type_args typ_vars typ_args params exprs var_env in
    let params = replace_generics params typ_vars typ_args in
    if not(List.fold_left (fun acc array_expr -> check_struct_literal params array_expr var_env && acc) true array_exprs) then raise_error ("?1")
    else typ_args
  ) with _ -> meme typ_vars typ_args params t var_env)
  | _::t -> meme typ_vars typ_args params t var_env
  
let declaration_type_check name vmod typ expr var_env = 
    if localvar_exists name var_env.locals then raise_error ("Duplicate variable name '" ^ name ^ "'")
    else match expr with
    | Value(StructLiteral(exprs)) -> ( match typ with
      | Some(T_Struct(name,typ_args)) -> ( match lookup_struct name var_env.structs with
        | Some(typ_vars,params) ->  (
          let typ_args = resolve_type_args typ_vars typ_args params exprs var_env in
          let params = replace_generics params typ_vars typ_args in
          if not(check_struct_literal params (Value (StructLiteral exprs)) var_env) then raise_error ("Could not match struct literal with '" ^ type_string (T_Struct(name,typ_args)) ^ "'")
          else (T_Struct(name,typ_args))
        )
        | None -> raise_error ("No such struct '" ^ name ^ "'")
      )
      | None -> raise_error "Struct literals cannot be infered to a type"
      | _ -> raise_error "Struct literal assigned to non-struct variable"
    )
    | Value(ArrayLiteral(exprs)) -> ( match typ with
      | Some(T_Array(Some(T_Struct(name, typ_args)))) -> ( match lookup_struct name var_env.structs with
        | Some(typ_vars,params) -> T_Array(Some(T_Struct(name, meme typ_vars typ_args params exprs var_env)))
        | None -> raise_error ("No such struct '" ^ name ^ "'")
      )
      | _ -> raise_error "Array literal assigned to non-array variable"
    )
    | _ -> (
      let (expr_vmod, expr_ty) = type_expr expr var_env in
      if (Option.is_none typ) && (expr_ty = T_Null) then raise_error "Cannot infere a type from 'null'" else
      let typ = if Option.is_some typ then (if well_defined_type (Option.get typ) var_env then Option.get typ else raise_error "Not a well defined type") else expr_ty in
      if vmod = Open && expr_vmod != Open then raise_error "Cannot assign a protected variable to an open variable"
      else if not (type_equal typ expr_ty) then raise_error ("Type mismatch: expected '" ^ (type_string typ) ^ "', got '" ^ (type_string expr_ty) ^ "'")
      else typ
    )

let argument_type_check vmod typ expr var_env = 
  match expr with
  | Value(StructLiteral(exprs)) -> ( match typ with
    | T_Struct(n,typ_args) -> ( match lookup_struct n var_env.structs with
      | Some(typ_vars,params) ->  (
        let typ_args = resolve_type_args typ_vars typ_args params exprs var_env in
        let params = replace_generics params typ_vars typ_args in
        if not(check_struct_literal params (Value(StructLiteral(exprs))) var_env) then raise_error ("Could not match struct literal with '" ^ type_string (T_Struct(n,typ_args)) ^ "'")
        else T_Struct(n,typ_args)
      )
      | None -> raise_error ("No such struct '" ^ n ^ "'")
    )
    | _ -> raise_error "Struct literal given as a non-struct argument"
  )
  | _ -> (
    let (expr_vmod, expr_ty) = type_expr expr var_env in
    if vmod = Open && (expr_vmod != Open) then raise_error "Cannot use a protected variable as an open variable"
    else if vmod = Stable && (expr_vmod = Const) then raise_error "Cannot use a constant variable as a stable parameter"
    else if not (type_equal typ expr_ty) then raise_error ("Type mismatch: expected '" ^ (type_string typ) ^ "', got '" ^ (type_string expr_ty) ^ "'")
    else typ
  )