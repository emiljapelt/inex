open Absyn
open ProgramRep

let lookup_routine (name: string) routines =
  let rec aux li =
    match li with
    | [] -> None
    | (n,ps)::t -> if n = name then Some(ps) else aux t
  in
  aux routines

let lookup_globvar (name: string) globvars =
  let rec aux li c =
    match li with
    | [] -> None
    | (n,c,l,ty,_)::t -> if n = name then Some((c,ty,l)) else aux t (c-1)
  in
  aux globvars ((List.length globvars) - 1)

let lookup_localvar (name: string) localvars =
  let rec aux li c =
    match li with
    | [] -> None
    | (l,ty,n)::t -> if n = name then Some((c,ty,l)) else aux t (c-1)
  in
  aux localvars ((List.length localvars) - 1)

let count_decl stmt_dec_list =
  let rec aux sdl c =
    match sdl with
    | [] -> c
    | h::t -> (
      match h with
      | Declaration _ -> aux t (c+1)
      | AssignDeclaration _ -> aux t (c+1)
      | VarDeclaration _ -> aux t (c+1)
      | _ -> aux t c
    )
  in
  aux stmt_dec_list 0

let type_string t =
  match t with
  | T_Bool -> "'bool'"
  | T_Int -> "'int'"

let routine_head accmod name params =
  match accmod with
  | Internal -> Label(name)
  | External -> EntryPoint(name, List.map (fun (l,t,n) -> t) params)

type label_generator = { mutable next : int }

let lg = ( {next = 0;} )

let new_label () =
  let number = lg.next in
  let () = lg.next <- lg.next+1 in
  Int.to_string number

let fetch_globvar_expr (name: string) globvars =
  let rec aux li =
    match li with
    | [] -> failwith ("No such global variable: " ^ name)
    | (n,_,_,_,expr)::t -> if n = name then expr else aux t
  in
  aux globvars

let var_index (name: string) globvars localvars = 
  match lookup_localvar name localvars with
  | Some (lc,_,_) -> lc
  | None -> 
    match lookup_globvar name globvars with
    | Some (gc,_,_) -> gc
    | None -> failwith ("No such variable " ^ name)

let fetch_var_index (name: string) globvars localvars = 
  match lookup_localvar name localvars with
  | Some (lc,_,_) -> IntInstruction(36, lc)
  | None -> 
    match lookup_globvar name globvars with
    | Some (gc,_,_) -> IntInstruction(35, gc)
    | None -> failwith ("No such variable " ^ name)

let fetch_var_val (name: string) globvars localvars = 
  let t = match lookup_localvar name localvars with
    | Some (_,lt,_) -> lt
    | None -> 
      match lookup_globvar name globvars with
      | Some (_,gt,_) -> gt
      | None -> failwith ("No such variable " ^ name)
  in
  match t with
  | T_Int -> (t, (fetch_var_index name globvars localvars) :: [Instruction(12)])
  | T_Bool -> (t, (fetch_var_index name globvars localvars) :: [Instruction(11)])

let var_locked (name: string) globvars localvars = 
  match lookup_localvar name localvars with
    | Some (_,_,ll) -> ll
    | None -> 
      match lookup_globvar name globvars with
      | Some (_,_,gl) -> gl
      | None -> failwith ("No such variable " ^ name)

let globvar_exists (name: string) globvars =
  match lookup_globvar name globvars with
  | Some _ -> true
  | None -> false
  
let localvar_exists (name: string) localvars =
  match lookup_localvar name localvars with
  | Some _ -> true
  | None -> false

let routine_exists (name: string) routines =
  match lookup_routine name routines with
  | Some _ -> true
  | None -> false


let default_value t =
  match t with
  | T_Int -> Int 0
  | T_Bool -> Bool false

(*    list of: string * int * bool * typ * assignable_expression    *)
let get_globvars (tds : topdecs) = 
  let rec aux topdecs acc count =
    match topdecs with
    | [] -> acc
    | h::t -> (
       match h with
      | Global (locked, ty, name) -> (
        if globvar_exists name acc then failwith ("Duplicate global variable name: " ^ name)
        else aux t ((name, count, locked, ty, (default_value ty))::acc) (count+1)
        )
      | GlobalAssign (locked, ty, name, a_expr) -> (
        if globvar_exists name acc then failwith ("Duplicate global variable name: " ^ name)
        else aux t ((name, count, locked, ty, a_expr)::acc) (count+1)
        )
      | _ -> aux t acc count
    )
  in match tds with 
  | Topdecs l -> aux l [] 0

(*    list of: string * access_mod * (typ * string) list * statement    *)
let get_routines (tds : topdecs) =
  let rec aux topdecs acc =
    match topdecs with
    | [] -> acc
    | h::t -> (
      match h with
      | Routine (accmod, name, params, stmt) -> (
        if routine_exists name acc then failwith ("Duplicate routine name: " ^ name)
        else aux t ((name, params)::acc)
        )
      | _ -> aux t acc
    )
  in match tds with
  | Topdecs l -> aux l []



let rec compile_assignable_expr expr globvars localvars =
  match expr with
  | Bool b -> (T_Bool, [BoolInstruction(5, b)])
  | Int i -> (T_Int, [IntInstruction(6, i)])
  | Lookup n -> fetch_var_val n globvars localvars
  | Binary_op (op, e1, e2) -> (
      let (t1, ins1) = compile_assignable_expr e1 globvars localvars in
      let (t2, ins2) = compile_assignable_expr e2 globvars localvars in
      match (op, t1, t2, e1, e2) with
      | ("&", T_Bool, T_Bool, Bool true, _) ->  (T_Bool, ins2)
      | ("&", T_Bool, T_Bool, _, Bool true) ->  (T_Bool, ins1)
      | ("&", T_Bool, T_Bool, Bool false, _) ->  (T_Bool, [BoolInstruction(5, false)])
      | ("&", T_Bool, T_Bool, _, Bool false) ->  (T_Bool, [BoolInstruction(5, false)])
      | ("&", T_Bool, T_Bool, _, _) ->  (T_Bool, ins1 @ ins2 @ [Instruction(24)])
      | ("|", T_Bool, T_Bool, Bool true, _) -> (T_Bool, [BoolInstruction(5, true)])
      | ("|", T_Bool, T_Bool, _, Bool true) -> (T_Bool, [BoolInstruction(5, true)])
      | ("|", T_Bool, T_Bool, Bool false, _) -> (T_Bool, ins2)
      | ("|", T_Bool, T_Bool, _, Bool false) -> (T_Bool, ins1)
      | ("|", T_Bool, T_Bool, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(25)])
      | ("=", T_Bool, T_Bool, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(22)])
      | ("!=", T_Bool, T_Bool, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(22)] @ [Instruction(23)])
      | ("=", T_Int, T_Int, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(20)])
      | ("!=", T_Int, T_Int, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(20)] @ [Instruction(23)])
      | ("<=", T_Int, T_Int, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(21)] @ [Instruction(23)]) 
      | ("<", T_Int, T_Int, _, _) -> (T_Bool, ins2 @ ins1 @ [Instruction(21)])
      | (">=", T_Int, T_Int, _, _) -> (T_Bool, ins2 @ ins1 @ [Instruction(21)] @ [Instruction(23)])
      | (">", T_Int, T_Int, _, _) -> (T_Bool, ins1 @ ins2 @ [Instruction(21)])
      | ("+", T_Int, T_Int, Int 0, _) -> (T_Int, ins2)
      | ("+", T_Int, T_Int, _, Int 0) -> (T_Int, ins1)
      | ("+", T_Int, T_Int, _, _) -> (T_Int, ins1 @ ins2 @ [Instruction(17)])
      | ("-", T_Int, T_Int, _, Int 0) -> (T_Int, ins1)
      | ("-", T_Int, T_Int, _, _) -> (T_Int, ins2 @ ins1 @ [Instruction(19)])
      | ("*", T_Int, T_Int, Int 0, _) -> (T_Int, [IntInstruction(6, 0)])
      | ("*", T_Int, T_Int, _, Int 0) -> (T_Int, [IntInstruction(6, 0)])
      | ("*", T_Int, T_Int, Int 1, _) -> (T_Int, ins2)
      | ("*", T_Int, T_Int, _, Int 1) -> (T_Int, ins1)
      | ("*", T_Int, T_Int, _, _) -> (T_Int, ins1 @ ins2 @ [Instruction(18)])
      | _ -> failwith "Unknown binary operator, or type mismatch"
    )
  | Unary_op (op, e) -> (
    let (t, ins) = compile_assignable_expr e globvars localvars in
    match (op, t) with
    | ("!", T_Bool) -> (T_Bool, ins @ [Instruction(23)])
    | _ -> failwith "Unknown unary operator, or type mismatch"
  )

let compile_arguments params exprs globvars localvars =
  let rec aux ps es acc =
    match (ps, es) with
    | ([],[]) -> acc
    | ((plock, pty, pname)::pt,eh::et) -> (
        let (ety, ins) = compile_assignable_expr eh globvars localvars in
        if pty != ety then failwith ("Type mismatch on assignment: expected " ^ (type_string pty) ^ ", got " ^ (type_string ety)) 
        else match eh with
        | Lookup n -> (
          match (plock, var_locked n globvars localvars) with
          | (false, true) -> failwith "Cannot give a locked variable as a parameter that is not locked"
          | _ -> aux pt et ((fetch_var_index n globvars localvars) :: acc)
        )
        | _ -> (
          match ety with
          | T_Int -> aux pt et (Instruction(14) :: Instruction(7) :: ins @ (Instruction(16) :: acc))
          | T_Bool -> aux pt et (Instruction(13) :: Instruction(7) :: ins @ (Instruction(15) :: acc))
        )
      )
    | _ -> failwith "Insufficient arguments in call"
  in
  aux params exprs []


let compile_unassignable_expr expr globvars localvars routines =
  match expr with
  | Assign (name, aexpr) -> (
    let (ty, ins) = compile_assignable_expr aexpr globvars localvars in
    let get = match lookup_localvar name localvars with
    | Some(cl,tl,ll) -> (
        if ll then failwith ("Cannot assign to locked variable: " ^ name)
        else if tl != ty then failwith ("Type mismatch on assignment: expected " ^ (type_string tl) ^ ", got " ^ (type_string ty)) 
        else IntInstruction(36, cl)
      )
    | None -> (
      match lookup_globvar name globvars with
      | Some(cg,tg,lg) -> (
        if lg then failwith ("Cannot assign to locked variable: " ^ name) 
        else if tg != ty then failwith ("Type mismatch on assignment: expected " ^ (type_string tg) ^ ", got " ^ (type_string ty))  
        else IntInstruction(35, cg)
      )
      | None -> failwith ("No such variable: " ^ name)
    )
    in match ty with
    | T_Bool -> get :: ins @ [Instruction(15)]
    | T_Int -> get :: ins @ [Instruction(16)]
  )
  | Call (n, aexprs) -> (
    match lookup_routine n routines with
    | None -> failwith ("No such routine: " ^ n)
    | Some (ps) when (List.length ps) = (List.length aexprs) -> (
      (compile_arguments ps aexprs globvars localvars) @ (IntInstruction(6, List.length ps) :: [LabelInstruction(2, n)])
    )
    | Some (ps) -> failwith (n ^ " requires " ^ (Int.to_string (List.length ps)) ^ " arguments, but was given " ^  (Int.to_string (List.length aexprs)))
  )
  | Stop -> [Instruction(1)]
  | Halt -> [Instruction(0)]
  | Print expr -> (
    let (t, ins) = compile_assignable_expr expr globvars localvars in
    match t with
    | T_Bool -> ins @ [Instruction(34)]
    | T_Int -> ins @ [Instruction(33)]
  )

let rec compile_sod_list sod_list globvars localvars routines =
  match sod_list with
  | [] -> []
  | h::t -> (
    match h with
    | Statement s -> compile_stmt s globvars localvars routines @ compile_sod_list t globvars localvars routines
    | Declaration (l, ty, n) -> (
      if localvar_exists n localvars then failwith ("Duplicate variable name: " ^ n)
      else match ty with
      | T_Int -> Instruction(14) :: Instruction(7) :: IntInstruction(6, 0) :: [Instruction(16)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
      | T_Bool -> Instruction(13) :: Instruction(7) :: BoolInstruction(5, false) :: [Instruction(15)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
    )
    | AssignDeclaration (l, ty, n, expr) -> (
      if localvar_exists n localvars then failwith ("Duplicate variable name: " ^ n)
      else let (expr_ty, ins) = compile_assignable_expr expr globvars localvars in
      match ty with
      | T_Int when expr_ty = T_Int -> Instruction(14) :: [Instruction(7)] @ ins @ [Instruction(16)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
      | T_Bool when expr_ty = T_Bool -> Instruction(13) :: [Instruction(7)] @ ins @ [Instruction(15)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
      | _ -> failwith ("Type mismatch on declaration: expected " ^ (type_string ty) ^ ", got " ^ (type_string expr_ty)) 
    )
    | VarDeclaration (l, n, expr) -> (
      if localvar_exists n localvars then failwith ("Duplicate variable name: " ^ n)
      else let (ty, ins) = compile_assignable_expr expr globvars localvars in
      match ty with
      | T_Int -> Instruction(14) :: [Instruction(7)] @ ins @ [Instruction(16)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
      | T_Bool -> Instruction(13) :: [Instruction(7)] @ ins @ [Instruction(15)] @ compile_sod_list t globvars ((l,ty,n)::localvars) routines
    )
  )

and compile_stmt stmt globvars localvars routines =
  match stmt with
  | If (e, s1, s2) -> (
    let label_name1 = new_label () in
    let label_name2 = new_label () in
    let (t, ins) = compile_assignable_expr e globvars localvars in
    if t != T_Bool then failwith "Conditional requires 'bool'"
    else ins @ [LabelInstruction(4, label_name1)] @ (compile_stmt s2 globvars localvars routines) @ [LabelInstruction(3,label_name2)] @ [Label(label_name1)] @ (compile_stmt s1 globvars localvars routines) @ [Label(label_name2)]
  )
  | While (e, s) -> (
    let label_cond = new_label () in
    let label_start = new_label () in
    let (t, ins) = compile_assignable_expr e globvars localvars in
    if t != T_Bool then failwith "Conditional requires 'bool'"
    else (LabelInstruction(3, label_cond)) :: Label(label_start) :: (compile_stmt s globvars localvars routines) @ [Label(label_cond)] @ ins @ [LabelInstruction(4, label_start)]
  )
  | Block (sod_list) -> (
    (compile_sod_list sod_list globvars localvars routines) @ [IntInstruction(31, (count_decl sod_list))]
  )
  | Expression (expr) -> compile_unassignable_expr expr globvars localvars routines

let rec evaluate_globvar used_vars expr globvars = 
  match expr with
  | Bool b -> Bool b
  | Int i -> Int i
  | Lookup n -> (
    if List.for_all (fun var -> n != var) used_vars then evaluate_globvar (n::used_vars) (fetch_globvar_expr n globvars) globvars
    else failwith "Cyclic referencing detected in global variables"
    )
  | Binary_op (op, e1, e2) -> (
      let v1 = evaluate_globvar used_vars e1 globvars in
      let v2 = evaluate_globvar used_vars e2 globvars in
      match (op, v1, v2) with
      | ("&", Bool b1, Bool b2) -> Bool (b1 && b2)
      | ("|", Bool b1, Bool b2) -> Bool (b1 || b2)
      | ("=", Bool b1, Bool b2) -> Bool (b1 = b2)
      | ("!=", Bool b1, Bool b2) -> Bool (b1 != b2)
      | ("=", Int i1, Int i2) -> Bool (i1 = i2)
      | ("!=", Int i1, Int i2) -> Bool (i1 != i2)
      | ("<=", Int i1, Int i2) -> Bool (i1 <= i2)
      | ("<", Int i1, Int i2) -> Bool (i1 < i2)
      | (">=", Int i1, Int i2) -> Bool (i1 >= i2)
      | (">", Int i1, Int i2) -> Bool (i1 > i2)
      | ("+", Int i1, Int i2) -> Int (i1 + i2)
      | ("-", Int i1, Int i2) -> Int (i1 - i2)
      | ("*", Int i1, Int i2) -> Int (i1 * i2)
      | _ -> failwith "Unknown binary operator, or type mismatch"
    )
  | Unary_op (op, e) -> (
    let v = evaluate_globvar used_vars e globvars in
    match (op, v) with
    | ("!", Bool b) -> Bool (not b)
    | _ -> failwith "Unknown unary operator, or type mismatch"
  )

let compile_globvars lst =
  let rec aux l acc = 
    match l with
    | [] -> acc
    | (n,_,l,ty,expr)::t -> (
      let v = evaluate_globvar [n] expr lst in
      match (ty, v) with
      | (T_Bool, Bool b) -> aux t ((G_Bool(b))::acc)
      | (T_Int, Int i) ->  aux t ((G_Int(i))::acc)
      | _ -> failwith ("Type mismatch in global variable: " ^ n)
    )
  in
  aux lst []

let compile topdecs =
  let globvars = get_globvars topdecs in
  let routines = get_routines topdecs in
  let rec aux tds acc =
    match tds with
    | [] -> acc
    | h::t -> match h with
      | Routine (accmod, n, params, stmt) -> 
        aux t ((routine_head accmod n params)::(compile_stmt stmt globvars params routines) @ [Instruction(1)] @ acc)
      | _ -> aux t acc
  in
  match topdecs with
  | Topdecs tds -> Program(compile_globvars globvars, aux tds [])