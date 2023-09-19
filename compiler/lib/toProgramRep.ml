open Absyn
open ProgramRep
open Exceptions
open Typing
open Helpers


(*** Helper functions ***)
let addFreeVars amount acc =
  match (amount, acc) with
  | (0, _) -> acc
  | (1, FreeVar :: accr) -> FreeVars(2) :: accr
  | (1, FreeVars(y) :: accr) -> FreeVars(y+1) :: accr
  | (1, _) -> FreeVar :: acc
  | (x, FreeVar :: accr) -> FreeVars(x+1) :: accr 
  | (x, FreeVars(y) :: accr) -> FreeVars(x+y) :: accr 
  | (x, _) -> FreeVars(x) :: acc

let addStop acc =
  match acc with
  | CStop::_ -> acc
  | CHalt::acc1 -> CStop :: acc1
  | _ -> CStop :: acc

let addHalt acc =
  match acc with
  | CHalt::_ -> acc
  | CStop::acc1 -> CHalt :: acc1
  | _ -> CHalt :: acc

(* Scanning *)
let count_decl stmt_dec_list =
  let rec aux sdl c =
    match sdl with
    | [] -> c
    | (Declaration(dec,_))::t -> (
      match dec with
      | TypeDeclaration _ -> aux t (c+1)
      | AssignDeclaration _ -> aux t (c+1)
    )
    | _::t -> aux t (c)
  in
  aux stmt_dec_list 0

(*    list of: string * access_mod * char list * (bool * typ * string) list * statement    *)
let get_routines file =
  let rec aux topdecs acc =
    match topdecs with
    | [] -> acc
    | h::t -> (
      match h with
      | Routine (accmod, name, typ_vars, params, stmt) -> (
        if routine_exists name acc then raise_error ("Duplicate routine name: " ^ name)
        else aux t ((accmod,name,"",typ_vars,params,stmt)::acc)
        )
      | _ -> aux t acc
    )
  in match file with
  | File (tds) -> aux tds []

(*    list of: string * char list * (bool * typ * string) list   *)
let get_structs file =
  let rec aux topdecs acc =
    match topdecs with
    | [] -> acc
    | h::t -> (
      match h with
      | Struct (name, typ_vars, params) -> (
        if struct_exists name acc then raise_error ("Duplicate struct name: " ^ name)
        else aux t ((name, typ_vars, params)::acc)
        )
      | _ -> aux t acc
    )
  in match file with
  | File (tds) -> aux tds []


(*** Global variable handling ***)
(*    Compute the list of variable dependencies for each global variable    *)
let get_globvar_dependencies gvs =
  let rec dependencies_from_assignable expr acc =
    match expr with
    | Reference r -> ( match r with
      | Null -> acc
      | OtherContext _ -> raise_error ("Global variables cannot depend on other contexts")
      | LocalContext(ref) -> ( match ref with
        | Access (name) -> name::acc
        | ArrayAccess (refer,_) -> dependencies_from_assignable (Reference(LocalContext refer)) acc
        | StructAccess (refer,_) -> dependencies_from_assignable (Reference(LocalContext refer)) acc
      )
    )
    | Value v -> ( match v with
      | Binary_op (_, expr1, expr2) -> dependencies_from_assignable expr1 (dependencies_from_assignable expr2 acc)
      | Unary_op (_, expr1) -> dependencies_from_assignable expr1 acc
      | ArraySize (refer) -> dependencies_from_assignable (Reference(LocalContext refer)) acc
      | Bool _ -> acc
      | Int _ -> acc
      | Char _ -> acc
      | GetInput _ -> acc
      | ValueOf (refer) -> dependencies_from_assignable (Reference(LocalContext refer)) acc
      | NewArray (_,expr1) -> dependencies_from_assignable expr1 acc
      | ArrayLiteral exprs -> List.fold_right (fun e a -> dependencies_from_assignable e a) exprs []
      | NewStruct (_,_,exprs) -> List.fold_right (fun e a -> dependencies_from_assignable e a) exprs []
      | StructLiteral (exprs) -> List.fold_right (fun e a -> dependencies_from_assignable e a) exprs []
    )
  in
  let dependencies_from_declaration dec =
    match dec with
    | TypeDeclaration _ -> []
    | AssignDeclaration (_,_,_,expr) -> dependencies_from_assignable expr []
  in
  List.map (fun (name,context_name,lock,ty,dec) -> ((name,context_name,lock,ty,dec), dependencies_from_declaration dec)) gvs

let extract_name t =
  match t with
  | (f,_,_,_,_,_) -> f

(*    Compute an ordering of the global variables, according to their dependencies    *)
let order_dep_globvars dep_gvs =
  let rec aux dep_globvars count prev_count remain acc =
    match dep_globvars with
    | [] when remain = [] -> acc
    | [] when count = prev_count -> raise_error "Could not resolve a global variable order, there might be a circular dependency"
    | [] -> aux remain count count [] acc
    | h::t -> ( match h with
      | ((name,context,lock,ty,dec), deps) -> (
        if List.for_all (fun dep -> List.exists (fun a -> dep = extract_name a) acc) deps then aux t (count+1) prev_count remain ((name,context,count,lock,ty,dec)::acc)
        else aux t count prev_count (h::remain) acc
      )
    )
  in
  List.rev (aux dep_gvs 0 0 [] [])

let gather_globvar_info gvs =
  List.map (fun (name,_,_,lock,ty,_) -> (lock, ty, name)) gvs


(*** Optimizing functions ***)
let rec optimize_assignable_expr expr var_env =
  match expr with
  | Reference _ -> expr
  | Value val_expr -> optimize_value val_expr var_env

and optimize_value expr var_env =
  match expr with
  | Binary_op (op, e1, e2) -> ( 
    let opte1 = optimize_assignable_expr e1 var_env in
    let opte2 = optimize_assignable_expr e2 var_env in
    match (op, opte1, opte2) with
    | ("&&", Value(Bool b1), Value(Bool b2)) -> Value(Bool(b1&&b2))
    | ("&&", Value(Bool true), _) -> opte2
    | ("&&", _, Value(Bool true)) -> opte1
    | ("&&", Value(Bool false), _) -> Value(Bool false)
    | ("&&", _, Value(Bool false)) -> Value(Bool false)
    | ("||", Value(Bool b1), Value(Bool b2)) -> Value(Bool(b1||b2))
    | ("||", Value(Bool true), _) -> Value(Bool true)
    | ("||", _, Value(Bool true)) -> Value(Bool true)
    | ("||", Value(Bool false), _) -> opte2
    | ("||", _, Value(Bool false)) -> opte1
    | ("+", Value(Int i1), Value(Int i2)) -> Value(Int (i1+i2))
    | ("+", Value(Int 0), _) -> opte2
    | ("+", _, Value(Int 0)) -> opte1
    | ("-", Value(Int 0), Value(Int i)) -> Value(Int (-i))
    | ("-", Value(Int i1), Value(Int i2)) -> Value(Int (i1-i2))
    | ("-", _, Value(Int 0)) -> opte1
    | ("*", Value(Int i1), Value(Int i2)) -> Value(Int (i1*i2))
    | ("*", Value(Int 0), _) -> Value(Int 0)
    | ("*", _, Value(Int 0)) -> Value(Int 0)
    | ("*", Value(Int 1), _) -> opte2
    | ("*", _, Value(Int 1)) -> opte1
    | ("=", Value(Int i1), Value(Int i2)) -> Value(Bool (i1=i2))
    | ("=", Value(Char c1), Value(Char c2)) -> Value(Bool (c1=c2))
    | ("=", Value(Bool b1), Value(Bool b2)) -> Value(Bool (b1=b2))
    | ("!=", Value(Int i1), Value(Int i2)) -> Value(Bool (i1!=i2))
    | ("!=", Value(Char c1), Value(Char c2)) -> Value(Bool (c1!=c2))
    | ("!=", Value(Bool b1), Value(Bool b2)) -> Value(Bool (b1!=b2))
    | ("<", Value(Int i1), Value(Int i2)) -> Value(Bool (i1<i2))
    | ("<=", Value(Int i1), Value(Int i2)) -> Value(Bool (i1<=i2))
    | (">", Value(Int i1), Value(Int i2)) -> Value(Bool (i1>i2))
    | (">=", Value(Int i1), Value(Int i2)) -> Value(Bool (i1>=i2))
    | _ -> Value(Binary_op(op, opte1, opte2))
  )
  | Unary_op (op, e) -> ( 
    let opte = optimize_assignable_expr e var_env in
    match (op, opte) with
    | ("!", Value(Bool b)) -> Value(Bool (not b))
    | _ -> opte
  )
  | ArraySize _ -> Value(expr)
  | GetInput _ -> Value(expr)
  | Bool _ -> Value(expr)
  | Int _ -> Value(expr)
  | Char _ -> Value(expr)
  | ValueOf _ -> Value(expr)
  | NewArray _ -> Value(expr)
  | ArrayLiteral _ -> Value(expr)
  | NewStruct (_,_,_) -> Value(expr)
  | StructLiteral(exprs) -> Value(StructLiteral( List.map (fun e -> optimize_assignable_expr e var_env) exprs ))


(*** Compiling functions ***)
let routine_head accmod name context base_context params =
  match accmod with
  | Internal -> CLabel(context^"#"^name)
  | External -> CLabel(context^"#"^name)
  | Entry -> (
    if (context = base_context) then CEntryPoint(name, (context^"#"^name), List.map (fun (lock,ty,_) -> (lock,ty)) params)
    else CLabel(context^"#"^name)
  )

let fetch_var_index (name: string) globvars localvars routines = 
  match lookup_localvar name localvars with
  | Some (lc,_,_) -> BPFetch(lc)
  | None -> 
    match lookup_globvar name globvars with
    | Some (gc,_,_) -> StackFetch(gc)
    | None -> match lookup_routine name routines with
      | Some (_,n,cn,_,_,_) -> CPlaceLabel(cn^"#"^n)
      | None -> raise_error ("No such variable '" ^ name ^ "'")

let rec compile_expr expr var_env acc =
  match expr with
  | Reference ref_expr -> compile_reference ref_expr var_env acc
  | Value val_expr -> compile_value val_expr var_env acc

and compile_inner_reference iref env contexts acc = 
  match iref with
  | Access name -> ( match lookup_localvar name env.var_env.locals with
    | Some _ -> (fetch_var_index name env.var_env.globals env.var_env.locals env.routine_env) :: RefFetch :: acc
    | None -> ( match lookup_globvar name env.var_env.globals with
      | Some _ -> (fetch_var_index name env.var_env.globals env.var_env.locals env.routine_env) :: RefFetch :: acc
      | None -> ( match lookup_routine (name) env.routine_env with
        | Some (_,_,cn,_,_,_) -> DeclareFull :: CloneFull :: DeclareFull :: CloneFull :: CPlaceLabel (cn^"#"^name) :: AssignFull :: AssignFull :: acc
        | None ->  raise_error ("Nothing exists by the name: " ^ name)
      )
    )
  )
  | StructAccess (refer, field) -> ( 
    let (_, ref_ty) = Typing.type_inner_reference refer env contexts in
    match ref_ty with
    | T_Struct (name, _) -> (
      match lookup_struct name env.var_env.structs with
      | Some (_, params) -> (
        let (_, _, index) = struct_field field params in
        compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: FieldFetch :: acc)
      )
      | None -> raise_error ("No such struct '" ^ name ^ "'")
    )
    | _ -> raise_error ("Struct field lookup on non-struct reference")
  )
  | ArrayAccess (refer, index) -> (
    let (_, ref_ty) = Typing.type_inner_reference refer env contexts in
    match ref_ty with
    | T_Array _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (FieldFetch :: acc)))
    | _ -> raise_error "Array acces to non-array reference"
  )

and compile_reference ref_expr (env : environment) contexts acc =
  match ref_expr with
  | Null -> PlaceFull(C_Int 0) :: acc
  | LocalContext ref -> compile_inner_reference ref env contexts acc
  | OtherContext(cn,ref) -> ( match lookup_context cn env.file_refs contexts with
    | None -> raise_error ("No such environment: " ^cn)
    | Some(env) -> compile_inner_reference ref env contexts acc
  )

and compile_expr_as_value expr (env : environment) contexts acc =
  match expr with
  | Reference r -> (
    let (_, ref_ty) = Typing.type_reference r env contexts in
    match ref_ty with
    | T_Int -> compile_reference r env contexts (FetchFull :: FetchFull :: acc)
    | T_Bool -> compile_reference r env contexts (FetchFull :: FetchByte :: acc)
    | T_Char -> compile_reference r env contexts (FetchFull :: FetchByte :: acc)
    | T_Array _ -> compile_reference r env contexts (FetchFull :: acc)
    | T_Struct _ -> compile_reference r env contexts (FetchFull :: acc)
    | T_Generic _ -> compile_reference r env contexts (FetchFull :: acc)
    | T_Null -> compile_reference r env contexts acc
    | T_Routine _ -> compile_reference r env contexts (FetchFull :: FetchFull :: acc)
  )
  | _ -> compile_expr expr env contexts acc

and compile_structure_arg arg idx var_env contexts acc =
  let (_, ha_ty) = Typing.type_expr arg var_env contexts in
  let optha = optimize_assignable_expr arg var_env in
  match optha with
  | Value _ -> (
    match ha_ty with
    | T_Int -> (CloneFull :: PlaceFull(C_Int idx) :: DeclareFull :: IncrRef :: CloneFull :: compile_expr optha var_env contexts (AssignFull :: FieldAssign :: acc))
    | T_Char -> (CloneFull :: PlaceFull(C_Int idx) :: DeclareFull :: IncrRef :: CloneFull :: compile_expr optha var_env contexts (AssignByte :: FieldAssign :: acc))
    | T_Bool -> (CloneFull :: PlaceFull(C_Int idx) :: DeclareFull :: IncrRef :: CloneFull :: compile_expr optha var_env contexts (AssignByte :: FieldAssign :: acc))
    | _ -> (CloneFull :: PlaceFull(C_Int idx) :: compile_expr optha var_env contexts (IncrRef :: FieldAssign :: acc))
  )
  | Reference r -> (
    match r with
    | Null -> (CloneFull :: PlaceFull(C_Int idx) :: compile_expr optha var_env contexts (FieldAssign :: acc))
    | _ -> (CloneFull :: PlaceFull(C_Int idx) :: compile_expr optha var_env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))
  )

and compile_structure args var_env contexts acc =
  PlaceFull(C_Int (List.length args)) :: DeclareStruct :: (List.fold_left (fun acc (arg, c) -> compile_structure_arg arg c var_env contexts acc) acc (List.mapi (fun i a -> (a,i)) args))

and compile_value val_expr var_env contexts acc =
  match val_expr with
  | Bool b -> PlaceByte(C_Bool b) :: acc
  | Int i -> PlaceFull(C_Int i) :: acc
  | Char c -> PlaceByte(C_Char c) :: acc
  | ArraySize refer -> (
    let (_, ref_ty) = Typing.type_inner_reference refer var_env contexts in
    match ref_ty with
    | T_Array _ -> compile_inner_reference refer var_env contexts (FetchFull :: SizeOf :: acc)
    | _ -> raise_error "Array size called on non-array value"
  )
  | GetInput ty -> ( match type_index ty with
    | -1 -> raise_error "Unsupported GetInput variant"
    | x -> GetInput(x) :: acc
  )
  | ValueOf refer -> (
    let (_, ref_ty) = Typing.type_inner_reference refer var_env contexts in
    match ref_ty with
    | T_Int -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Bool -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Char -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Array _ -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Struct _ -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Generic _ -> compile_expr_as_value (Reference(LocalContext refer)) var_env contexts acc
    | T_Null -> raise_error ("Direct null pointer dereferencing")
    | T_Routine _ -> raise_error ("Cannot take the value of a routine")
  )
  | NewArray (_, size_expr) -> (
    let (_, s_ty) = Typing.type_expr size_expr var_env contexts in
    match s_ty with
    | T_Int -> compile_expr_as_value (optimize_assignable_expr size_expr var_env) var_env contexts (DeclareStruct :: IncrRef :: acc)
    | _ -> raise_error ("Initializing array with non-integer size")
  )
  | ArrayLiteral exprs 
  | NewStruct (_, _, exprs)
  | StructLiteral (exprs) -> compile_structure exprs var_env contexts acc 
  | Binary_op (op, e1, e2) -> (
      let (_, t1) = Typing.type_expr e1 var_env contexts in
      let (_, t2) = Typing.type_expr e2 var_env contexts in
      match (op, t1, t2, e1, e2) with
      | ("&&", T_Bool, T_Bool, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts(BoolAnd :: acc))
      | ("||", T_Bool, T_Bool, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (BoolOr :: acc))
      | ("=", _, _, Reference(r), Reference(Null)) -> compile_reference r var_env contexts (FetchFull :: PlaceFull(C_Int 0) :: FullEq :: acc)
      | ("=", _, _, Reference(Null), Reference(r)) -> compile_reference r var_env contexts (FetchFull :: PlaceFull(C_Int 0) :: FullEq :: acc)
      | ("=", T_Bool, T_Bool, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (BoolEq :: acc))
      | ("=", T_Char, T_Char, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (ByteEq :: acc))
      | ("=", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (FullEq :: acc))
      | ("!=", _, _, Reference(r), Reference(Null)) -> compile_reference r var_env contexts (FetchFull :: PlaceFull(C_Int 0) :: FullEq :: BoolNot :: acc)
      | ("!=", _, _, Reference(Null), Reference(r)) -> compile_reference r var_env contexts (FetchFull :: PlaceFull(C_Int 0) :: FullEq :: BoolNot :: acc)
      | ("!=", T_Bool, T_Bool, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (BoolEq :: BoolNot :: acc))
      | ("!=", T_Char, T_Char, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (ByteEq :: BoolNot :: acc))
      | ("!=", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (FullEq :: BoolNot :: acc))
      | ("<=", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (IntLt :: BoolNot :: acc))
      | ("<", T_Int, T_Int, _, _) -> compile_expr_as_value e2 var_env contexts (compile_expr_as_value e1 var_env contexts (IntLt :: acc))
      | (">=", T_Int, T_Int, _, _) -> compile_expr_as_value e2 var_env contexts (compile_expr_as_value e1 var_env contexts (IntLt :: BoolNot :: acc))
      | (">", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (IntLt :: acc))
      | ("+", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (IntAdd :: acc))
      | ("-", T_Int, T_Int, _, _) -> compile_expr_as_value e2 var_env contexts (compile_expr_as_value e1 var_env contexts (IntSub :: acc))
      | ("*", T_Int, T_Int, _, _) -> compile_expr_as_value e1 var_env contexts (compile_expr_as_value e2 var_env contexts (IntMul :: acc))
      | _ -> raise_error "Unknown binary operator, or type mismatch"
    )
  | Unary_op (op, e) -> (
    let (_, t) = Typing.type_expr e var_env contexts in
    match (op, t, e) with
    | ("!", T_Bool, _) -> compile_expr_as_value e var_env contexts (BoolNot :: acc)
    | _ -> raise_error "Unknown unary operator, or type mismatch"
  )

let compile_arguments args (env : environment) contexts acc =
  let rec aux ars acc =
    match ars with
    | ([]) -> acc
    | (((pmod, pty),eh)::t) -> (
      let opteh = optimize_assignable_expr eh env.var_env in
      let typ = argument_type_check pmod (Some pty) opteh env contexts in
      match opteh with
      | Value _ -> ( match typ with
        | T_Int -> aux t (DeclareFull :: IncrRef :: CloneFull :: (compile_expr_as_value opteh env contexts (AssignFull :: acc)))
        | T_Bool -> aux t (DeclareByte :: IncrRef :: CloneFull :: (compile_expr_as_value opteh env contexts (AssignByte :: acc)))
        | T_Char -> aux t (DeclareByte :: IncrRef :: CloneFull :: (compile_expr_as_value opteh env contexts (AssignByte :: acc)))
        | T_Array _ -> aux t (compile_expr_as_value opteh env contexts (IncrRef :: acc))
        | T_Struct _ -> aux t (compile_expr_as_value opteh env contexts (IncrRef :: acc))
        | T_Null -> aux t (compile_expr_as_value opteh env contexts (acc))
        | T_Generic _ -> aux t (compile_expr_as_value opteh env contexts (IncrRef :: acc))
        | T_Routine _ -> aux t (DeclareFull :: IncrRef :: CloneFull :: (compile_expr_as_value opteh env contexts (AssignFull :: acc)))
      )
      | Reference r -> (match r with
        | LocalContext ref -> ( match ref with
          | Access _ -> aux t (compile_inner_reference ref env contexts (IncrRef :: acc)) 
          | StructAccess _ -> aux t (compile_inner_reference ref env contexts (FetchFull :: IncrRef :: acc)) 
          | ArrayAccess _ -> aux t (compile_inner_reference ref env contexts (FetchFull :: IncrRef :: acc)) 
        )
        | OtherContext (cn,ref) -> ( match lookup_context cn env.file_refs contexts with
          | None -> raise_error ("No such context:"^cn)
          | Some(env) -> ( match ref with
            | Access _ -> aux t (compile_inner_reference ref env contexts (IncrRef :: acc)) 
            | StructAccess _ -> aux t (compile_inner_reference ref env contexts (FetchFull :: IncrRef :: acc)) 
            | ArrayAccess _ -> aux t (compile_inner_reference ref env contexts (FetchFull :: IncrRef :: acc)) 
          )
        )
        | Null -> aux t (compile_reference r env contexts acc) 
      )
    )
  in
  aux (List.rev args) acc

let compile_assignment target assign (env : environment) contexts acc =
  let assign_type = Typing.assignment_type_check target assign env contexts in
  match target, assign with
  | (Null, _) -> raise_error "Assignment to null"
  | (OtherContext _, _) -> raise_error "Assignment to other context"
  | (LocalContext(Access _), Value v) -> ( match assign_type with 
    | T_Int ->  compile_reference target env contexts (FetchFull :: (compile_value v env contexts (AssignFull :: acc)))
    | T_Bool -> compile_reference target env contexts (FetchFull :: (compile_value v env contexts (AssignByte :: acc)))
    | T_Char -> compile_reference target env contexts (FetchFull :: (compile_value v env contexts (AssignByte :: acc)))
    | T_Array _ -> compile_reference target env contexts (compile_value v env contexts (IncrRef :: RefAssign :: acc))
    | T_Struct _ -> compile_reference target env contexts (compile_value v env contexts (IncrRef :: RefAssign :: acc))
    | T_Null -> compile_reference target env contexts (compile_value v env contexts (RefAssign :: acc))
    | T_Generic _ -> compile_reference target env contexts (compile_value v env contexts (IncrRef :: RefAssign :: acc))
    | T_Routine _ -> raise_error "There is no Values of this type yet"
  )
  | (LocalContext(Access _), Reference re) -> ( match assign_type with 
    | T_Int -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Bool -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Char -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Array _ -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Struct _ -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Null -> compile_reference target env contexts (compile_reference re env contexts (RefAssign :: acc))
    | T_Generic _ -> compile_reference target env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
    | T_Routine _ -> compile_reference target env contexts (FetchFull :: compile_reference re env contexts (FetchFull :: IncrRef :: RefAssign :: acc))
  )
  | (LocalContext(StructAccess(refer, field)), Value v) -> ( match Typing.type_inner_reference refer env contexts with
    | (_,T_Struct (str_name, _)) -> ( match lookup_struct str_name env.var_env.structs with
      | None -> raise_error ("Could not find struct '" ^ str_name ^ "'")
      | Some (_, fields) -> ( match struct_field field fields with
        | (_,_,index) -> ( match assign_type with
          | T_Int -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: FieldFetch :: FetchFull :: (compile_value v env contexts (AssignFull :: acc)))
          | T_Bool -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: FieldFetch :: FetchFull :: (compile_value v env contexts (AssignByte :: acc)))
          | T_Char -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: FieldFetch :: FetchFull :: (compile_value v env contexts (AssignByte :: acc)))
          | T_Array _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_value v env contexts (IncrRef :: FieldAssign :: acc)))
          | T_Struct _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_value v env contexts (IncrRef :: FieldAssign :: acc)))
          | T_Null  -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_value v env contexts (FieldAssign :: acc)))
          | T_Generic _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_value v env contexts (IncrRef :: FieldAssign :: acc)))
          | T_Routine _ -> raise_error "There is no Values of this type yet"
        )
      )
    )
    | (_,t) -> raise_error ("Struct field assignment to variable of type '" ^ Typing.type_string t ^ "'") 
  )
  | (LocalContext(StructAccess(refer, field)), Reference re) -> ( match Typing.type_inner_reference refer env contexts with
    | (_,T_Struct (str_name, _)) -> ( match lookup_struct str_name env.var_env.structs with
      | None -> raise_error ("Could not find struct '" ^ str_name ^ "'")
      | Some (_, fields) -> ( match struct_field field fields with
        | (_, _, index) -> ( match assign_type with
          | T_Int -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Bool -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Char -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Array _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Struct _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Null  -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FieldAssign :: acc)))
          | T_Generic _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
          | T_Routine _ -> compile_inner_reference refer env contexts (FetchFull :: PlaceFull(C_Int index) :: (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc)))
        )
      )
    )
    | (_,t) -> raise_error ("Struct field assignment to variable of type '" ^ Typing.type_string t ^ "'") 
  )
  | (LocalContext(ArrayAccess(refer, index)), Value v) -> ( match Typing.type_inner_reference refer env contexts with
    | (_,T_Array _) -> ( match Typing.type_expr index env contexts with
      | (_,T_Int) -> ( match assign_type with
        | T_Int -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (FieldFetch :: FetchFull :: (compile_value v env contexts (AssignFull :: acc)))))
        | T_Bool -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (FieldFetch :: FetchFull :: (compile_value v env contexts (AssignByte :: acc)))))
        | T_Char -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (FieldFetch :: FetchFull :: (compile_value v env contexts (AssignByte :: acc)))))
        | T_Array _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_value v env contexts (IncrRef :: FieldAssign :: acc))))
        | T_Struct _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_value v env contexts (IncrRef :: FieldAssign :: acc))))
        | T_Null -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_value v env contexts (FieldAssign :: acc))))
        | T_Generic _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_value v env contexts (IncrRef :: FieldAssign :: acc))))
        | T_Routine _ -> raise_error "There is no Values of this type yet"
      )
      | (_,_) -> raise_error "Array index must be of type 'int'"
    )
    | (_,t) -> raise_error ("Array assignment to variable of type '" ^ Typing.type_string t ^ "'") 
  )
  | (LocalContext(ArrayAccess(refer, index)), Reference re) -> ( match Typing.type_inner_reference refer env contexts with
    | (_,T_Array _) -> ( match Typing.type_expr index env contexts with 
      | (_,T_Int) -> ( match assign_type with
        | T_Int -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Bool -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Char -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Array _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Struct _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Null -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FieldAssign :: acc))))
        | T_Generic _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
        | T_Routine _ -> compile_inner_reference refer env contexts (FetchFull :: (compile_expr_as_value index env contexts (compile_reference re env contexts (FetchFull :: IncrRef :: FieldAssign :: acc))))
      )
      | (_,_) -> raise_error "Array index must be of type 'int'"
    )
    | (_,t) -> raise_error ("Array assignment to variable of type '" ^ Typing.type_string t ^ "'") 
  )
  

let update_locals env (vmod : var_mod) typ name =
  ({ env with var_env = ({ env.var_env with locals = (vmod, typ, name)::env.var_env.locals }) })

let compile_declaration dec env contexts =
  match dec with
  | TypeDeclaration (vmod, typ, name) -> (
    if localvar_exists name env.var_env.locals then raise_error ("Duplicate variable name '" ^ name ^ "'")
    else if not(well_defined_type (Some typ) env.var_env) then raise_error "Ill defined type"
    else 
    ( update_locals env vmod typ name,
      match typ with
      | T_Int -> fun a -> DeclareFull :: IncrRef :: CloneFull :: PlaceFull(C_Int 0) :: AssignFull :: a
      | T_Bool -> fun a -> DeclareByte :: IncrRef :: CloneFull :: PlaceByte(C_Bool false) :: AssignByte :: a
      | T_Char -> fun a -> DeclareByte :: IncrRef :: CloneFull :: PlaceByte(C_Char '0') :: AssignByte :: a
      | T_Array _
      | T_Struct _
      | T_Routine _ 
      | T_Generic _ -> fun a -> PlaceFull(C_Int 0) :: a
      | T_Null -> raise_error "Cannot declare the 'null' type"
    )
  )
  | AssignDeclaration (vmod, typ, name, expr) -> (
    if localvar_exists name env.var_env.locals then raise_error ("Duplicate variable name '" ^ name ^ "'") ;
    let opt_expr = optimize_assignable_expr expr env.var_env in
    let typ = declaration_type_check vmod typ expr env contexts in
    ( update_locals env vmod typ name,
      match opt_expr with
      | Reference(LocalContext(Access _)) -> fun a -> compile_expr opt_expr env contexts (FetchFull :: IncrRef :: a)
      | Reference(OtherContext(_, Access _)) -> fun a -> compile_expr opt_expr env contexts (FetchFull :: IncrRef :: a)
      | Reference _ -> fun a -> compile_expr opt_expr env contexts (IncrRef :: a)
      | Value _ -> (
        match typ with
        | T_Int -> fun a -> DeclareFull :: IncrRef :: CloneFull :: (compile_expr opt_expr env contexts (AssignFull :: a))
        | T_Bool -> fun a -> DeclareByte :: IncrRef :: CloneFull :: (compile_expr opt_expr env contexts (AssignByte :: a))
        | T_Char -> fun a -> DeclareByte :: IncrRef :: CloneFull :: (compile_expr opt_expr env contexts (AssignByte :: a))
        | T_Array _ -> fun a -> compile_expr opt_expr env contexts (IncrRef :: a)
        | T_Struct _ -> fun a -> compile_expr opt_expr env contexts (IncrRef :: a)
        | T_Generic _ -> fun a -> compile_expr opt_expr env contexts (IncrRef :: a)
        | T_Null -> fun a -> compile_expr opt_expr env contexts a
        | T_Routine _ -> raise_error "There is no Values of this type yet"
      )
    )
  )

let rec compile_sod_list sod_list env contexts break continue cleanup acc =
  match sod_list with
  | [] -> acc
  | h::t -> (
    match h with
    | Statement(stmt, line) -> ( try (
        compile_stmt stmt env contexts break continue cleanup (compile_sod_list t env contexts break continue cleanup (acc))
      ) with
      | Error(_,line_opt,expl) when Option.is_none line_opt -> raise (Error(None, Some(line), expl))
      | e -> raise e
    )
    | Declaration(dec, line) -> ( try (
        let (new_env, f) = compile_declaration dec env contexts in
        f (compile_sod_list t new_env contexts break continue (cleanup+1) acc)
      ) with
      | Error(_,line_opt,expl) when Option.is_none line_opt -> raise (Error(None, Some(line), expl))
      | e -> raise e
    )
  )

and compile_stmt stmt env contexts break continue cleanup acc =
  match stmt with
  | If (expr, s1, s2) -> (
    let label_true = Helpers.new_label () in
    let label_stop = Helpers.new_label () in
    let (_, t) = Typing.type_expr expr env contexts in
    if t != T_Bool then raise_error "Condition not of type 'bool'"
    else compile_expr_as_value expr env contexts (IfTrue(label_true) :: (compile_stmt s2 env contexts break continue cleanup (GoTo(label_stop) :: CLabel(label_true) :: (compile_stmt s1 env contexts break continue cleanup (CLabel(label_stop) :: acc)))))
  )
  | While (expr, s) -> (
    let label_cond = Helpers.new_label () in
    let label_start = Helpers.new_label () in
    let label_stop = Helpers.new_label () in
    let (_, t) = Typing.type_expr expr env contexts in
    if t != T_Bool then raise_error "Condition not of type 'bool'"
    else GoTo(label_cond) :: CLabel(label_start) :: (compile_stmt s env contexts (Some label_stop) (Some label_cond) 0 (CLabel(label_cond) :: (compile_expr_as_value expr env contexts (IfTrue(label_start) :: CLabel(label_stop) :: acc))))
  )
  | Block (sod_list) -> (
    let decs = count_decl sod_list in
    if decs = 0 then compile_sod_list sod_list env contexts break continue cleanup acc
    else compile_sod_list sod_list env contexts break continue cleanup (addFreeVars decs acc)
  )
  | Assign (target, aexpr) -> compile_assignment (LocalContext target) (optimize_assignable_expr aexpr env.var_env) env contexts acc
  | Call (ref, typ_args, args) -> ( 
    let (typ_vars,params,call_f,env) = match ref with
    | Null -> raise_error ("Null call")
    | OtherContext (cn,Access n) -> ( match lookup_context cn env.file_refs contexts with
      | None -> raise_error ("No such context: "^cn)
      | Some(env) -> match lookup_routine n env.routine_env with
        | None -> raise_error ("No such routine '" ^n^ "' in context '" ^cn^ "'" )
        | Some(Internal,_,_,_,_,_) -> raise_error ("Call to internal routine of other context")
        | Some(_,_,_,tvs,ps,_) -> (tvs,List.map (fun (a,b,_) -> (a,b)) ps, (fun acc -> CPlaceLabel((env.context_name)^"#"^n) :: Call :: acc),env)
    )
    | LocalContext(Access n) -> ( 
      if (localvar_exists n env.var_env.locals) || (globvar_exists n env.var_env.globals) then match type_inner_reference (Access n) env contexts with
        | (_, T_Routine ts) -> ([], ts, (fun acc -> compile_expr_as_value (Reference ref) env contexts (Call :: acc)), env)
        | _ -> raise_error "Call to non-routine value"
      else match lookup_routine n env.routine_env with
      | None -> raise_error ("No such routine '" ^n^ "' in context '" ^env.context_name^ "'" )
      | Some(_,_,_,tvs,ps,_) -> (tvs,List.map (fun (a,b,_) -> (a,b)) ps, (fun acc -> CPlaceLabel((env.context_name)^"#"^n) :: Call :: acc),env)
    )
    | LocalContext(access) -> ( match type_inner_reference access env contexts with
      | (_, T_Routine ts) -> ([], ts, (fun acc -> compile_inner_reference access env contexts (FetchFull :: FetchFull :: Call :: acc)), env)
      | _ -> raise_error "Call to non-routine value"
    )
    | _ -> raise_error "Illegal call"
    in
    if List.length params != List.length args then raise_error ("Call requires " ^ (Int.to_string (List.length params)) ^ " arguments, but was given " ^  (Int.to_string (List.length args)))
    else if typ_vars = [] then compile_arguments (List.combine params args) env contexts (PlaceFull(C_Int (List.length params)) :: call_f acc) 
    else (
      let typ_args = resolve_type_args typ_vars typ_args params args env contexts in
      compile_arguments (List.combine (replace_generics params typ_vars typ_args) args) env contexts (PlaceFull(C_Int (List.length params)) :: call_f acc)
    )
  )
  | Stop -> addStop(acc)
  | Halt -> addHalt(acc)
  | Break -> (
    match break with
    | Some name when cleanup = 0 -> GoTo(name) :: acc
    | Some name -> addFreeVars cleanup (GoTo(name) :: acc)
    | None -> raise_error "No loop to break out of"
  )
  | Continue -> (
    match continue with
    | Some name when cleanup = 0 -> GoTo(name) :: acc
    | Some name -> addFreeVars cleanup (GoTo(name) :: acc)
    | None -> raise_error "No loop to continue in"
  )
  | Print exprs -> (
    let rec aux es acc =
      match es with
      | [] -> acc
      | h::t -> (
        let (_, expr_ty) = Typing.type_expr h env contexts in
        let opte = optimize_assignable_expr h env.var_env in
        match expr_ty with
        | T_Bool -> aux t (compile_expr_as_value opte env contexts (PrintBool :: acc))
        | T_Int -> aux t (compile_expr_as_value opte env contexts (PrintInt :: acc))
        | T_Char -> aux t (compile_expr_as_value opte env contexts (PrintChar :: acc))
        | _ -> aux t (compile_expr opte env contexts (PrintInt :: acc))
      )
    in
    aux (List.rev exprs) acc
  )

let rec compile_globalvars globvars structs contexts acc =
  match globvars with
  | [] -> acc
  | (_,context_name,_,_,_,dec)::t -> (
    try (
      match List.find_opt (fun c -> match c with Context(name,_) -> name = context_name) contexts with
      | None -> raise_error "Failed context lookup"
      | Some(Context(_,env)) -> (
        let (_,f) = compile_declaration dec ({ context_name = context_name;  var_env = ({ locals = []; globals = env.var_env.globals; structs = structs; typ_vars = []}); routine_env = []; file_refs = [] }) contexts in
        compile_globalvars t structs contexts (f acc)
      )
    )
    with
    | e -> raise e
  )

let compress_path path =
  let rec compress parts acc =
    match parts with
    | [] -> List.rev acc
    | h::t when h = "." -> compress t (acc)
    | _::h2::t when h2 = ".." -> compress t acc
    | h::t -> compress t (h::acc) 
  in
  String.concat "/" (compress (String.split_on_char '/' path) [])

let total_path path =
  if path.[0] = '.' then Sys.getcwd () ^ "/" ^ path
  else path

let complete_path base path = compress_path (if path.[0] = '.' then (String.sub base 0 ((String.rindex base '/')+1) ^ path) else path)

let gather_context_infos base_path parse =
  let rec get_context_environment path topdecs file_refs globals structs routines =
    match topdecs with
    | [] -> (complete_path base_path path, globals, structs, routines, file_refs)
    | (FileReference(alias, ref_path))::t -> (
      if List.exists (fun (a,_) -> a = alias) file_refs then raise_error ("Duplicate context alias '" ^ alias ^ "'") else
      let ref_path = complete_path path ref_path in
      get_context_environment path t ((alias,ref_path)::file_refs) globals structs routines
    )
    | (Routine(access_mod, name, typ_vars, params, stmt))::t -> get_context_environment path t file_refs globals structs ((access_mod,name,(complete_path base_path path),typ_vars,params,stmt)::routines)
    | (Struct(name, typ_vars, fields))::t -> get_context_environment path t file_refs globals ((name, typ_vars, fields)::structs) routines
    | (GlobalDeclaration(declaration))::t -> ( match declaration with
      | TypeDeclaration(vmod, typ, name) -> get_context_environment path t file_refs ((name,(complete_path base_path path),vmod,typ,declaration)::globals) structs routines
      | AssignDeclaration(vmod, typ_opt, name, _) -> ( match typ_opt with
        | Some(typ) -> get_context_environment path t file_refs ((name,(complete_path base_path path),vmod,typ,declaration)::globals) structs routines
        | None -> raise_error "Cannot infere types for global variables"
      )
    )
  in
  let rec get_contexts path parse acc =
    let path = complete_path base_path path in
    let file = parse path in
    let context_env = get_context_environment path (match file with File(t) -> t) [][][][] in
    let (_,_,_,_,file_refs) = context_env in
    List.fold_right (fun (_,ref_path) acc -> 
      if List.exists (fun (_,(p,_,_,_,_)) -> p = ref_path) acc then acc
      else get_contexts ref_path parse (acc)
    ) file_refs ((file,context_env)::acc)
  in
  get_contexts base_path parse []

let merge_contexts contexts =
  let rec aux cs topdecs globals structs =
    match cs with
    | [] -> (File(topdecs), globals, structs)
    | (File(tds),(_,c_globals,c_structs,_,_))::t -> (
      aux t 
        (List.rev_append topdecs tds) 
        (List.rev_append globals c_globals) 
        (List.rev_append structs c_structs) 
    )
  in
  aux contexts [][][]

let create_contexts globals context_infos : context list =
  let get_globalvar_info var_name context_name = 
    match List.find_opt (fun (n,cn,_,_,_,_) -> n = var_name && cn = context_name) globals with
    | None -> raise_error "Failed global variable lookup"
    | Some((n,cn,idx,vmod,typ,dec)) -> (n,cn,idx,vmod,typ,dec)
  in
  let rec aux c_infos acc =
    match c_infos with
    | [] -> acc
    | (_,(context_name, globs, structs, routines, file_refs))::t -> (
      aux t (Context(context_name, ({ context_name = context_name; var_env = { locals = []; globals = (List.map (fun (n,cn,_,_,_) -> get_globalvar_info n cn) globs); structs = structs; typ_vars = []}; routine_env = routines; file_refs = file_refs }))::acc)
    )
  in
  aux context_infos []

let compile path parse =
  let path = (compress_path (total_path path)) in
  let context_infos = gather_context_infos path parse in
  let (topdecs,globals,structs) = merge_contexts context_infos in
  let globals_ordered = (order_dep_globvars (get_globvar_dependencies globals)) in
  let contexts = create_contexts globals_ordered context_infos in
  let () = check_topdecs topdecs structs in
  let () = check_structs structs in
  let rec compile_routines rs env acc =
    match rs with
    | [] -> acc
    | (accmod,name,context_name,typ_vars,params,body)::t -> compile_routines t env (((routine_head accmod name context_name path params)::(compile_stmt body ({ context_name = context_name; var_env = ({ locals = (List.rev params); globals = env.var_env.globals; structs = structs; typ_vars = typ_vars}); routine_env = env.routine_env; file_refs = env.file_refs}) contexts None None 0 (addStop(acc)))))
  in
  let rec compile_contexts cs acc =
    match cs with
    | [] -> acc
    | Context(_, env)::t -> compile_contexts t (compile_routines env.routine_env env acc)
  in
  let compile_main cts =
    try (
      compile_contexts cts []
    ) with
    | Error(_,line_opt,expl_opt) -> raise (Error(Some(path),line_opt,expl_opt))
  in
  Program(structs, (gather_globvar_info (match (List.find (fun c -> match c with Context(cn,_) -> cn = path) contexts) with Context(_,env) -> env.var_env.globals)), ProgramRep.translate(compile_globalvars (List.rev globals_ordered) structs contexts ((ToStart :: (compile_main contexts)))))