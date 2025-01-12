open Printf
open ProgramRep
open Exceptions

(* HELPERS *)

let write_word file w =
  for i = 0 to 7 do
    fprintf file "%c" (Char.chr (Int64.to_int (Int64.logand 255L (Int64.shift_right w (i * 8)))))
  done

let count_entry_points program =
  let rec aux p acc =
    match p with
    | [] -> acc
    | (Entry,_,_,_,_)::t -> aux t (acc+1)
    | _::t -> aux t acc
  in
  aux program 0

let rec retrieve_labels program c acc =
    match program with
    | [] -> acc
    | h::t -> (
      match h with
      | Label (s) -> retrieve_labels t c ((s, c)::acc)
      | FullInstruction _ -> retrieve_labels t (c+9) acc
      | ByteInstruction _ -> retrieve_labels t (c+2) acc
      | LabelInstruction _ -> retrieve_labels t (c+9) acc
      | PlaceLabel _ -> retrieve_labels t (c+9) acc
      | _ -> retrieve_labels t (c+1) acc
    )

let retrieve_structs program =
  match program with
  | Program (strs,_,_) -> strs

let retrieve_global_vars program =
  match program with
  | Program (_,gvs,_) -> gvs

let retrieve_program_parts program =
  match program with
  | Program (_,_,p) -> p

let get_index list prop =
  let rec aux l acc =
    match l with
    | [] -> None
    | h::t -> if prop(h) then Some acc else aux t (acc+1)
  in
  aux list 0


(* Writers *)

let variable_mod vmod =
  match vmod with
  | Open -> "\x00"
  | Stable -> "\x01"
  | Const -> "\x02"

let rec write_type_info file vmod ty structs =
  let rec write_type ty =
    fprintf file "%c" (Char.chr (ProgramRep.type_index ty)) ; 
    match ty with
    | T_Array sub -> write_type (Option.get sub)
    | T_Generic(c) -> fprintf file "%c" c;
    | T_Struct (str_name, _) -> (
      match get_index structs (fun (name, _, _) -> str_name = name) with
      | None -> failwith "struct not found while writing binary"
      | Some i -> write_word file (Int64.of_int i)
    )
    | T_Routine(_,params) -> (
      fprintf file "%c" (Char.chr (List.length params));
      params 
      |> List.map (fun (vm, ty_opt) -> (vm, Option.get ty_opt)) 
      |> List.iter (fun (vm,t) -> write_type_info file vm t structs );
    )
    | _ -> ()
  in
  fprintf file "%s" (variable_mod vmod) ;
  write_type ty

let write_typ_vars file typ_vars =
  let rec aux tvs =
    match tvs with
    | [] -> ()
    | h::t -> fprintf file "%c" h ; aux t
  in
  fprintf file "%c" (Char.chr (List.length typ_vars)) ;
  aux typ_vars

let write_entry_point_info file name addr args structs =
  fprintf file "%s%c" name '\x00';
  write_word file (Int64.of_int addr);
  fprintf file "%c" (Char.chr (List.length args));
  let rec print_args a = 
    match a with
    | [] -> ()
    | (vmod,ty)::t -> write_type_info file vmod ty structs ; print_args t
  in
  args |> List.map (fun (vm, ty_opt) -> (vm, Option.get ty_opt)) |> print_args


(* (access_mod * var_mod * typ * string) list *)
let write_entry_points file globs structs =
  write_word file (Int64.of_int (count_entry_points globs)) ;
  let rec aux globs =
    match globs with
    | [] -> ()
    | (Entry,_,Some T_Routine(_,ps),idx,name)::t -> 
      write_entry_point_info file name idx ps structs ; aux t
    | _::t -> aux t
  in
  aux globs



let write_global_var_info file name lock ty structs =
  fprintf file "%s%c" name '\x00' ; write_type_info file lock ty structs

let write_global_vars file gvs structs =
  write_word file (Int64.of_int (List.length gvs)) ;
  let rec aux gs = 
    match gs with
    | [] -> ()
    | (_,varmod,Some ty,_,name)::t -> write_global_var_info file name varmod ty structs ; aux t
    | (_,_,None,_,name)::_ -> raise_failure ("unset type: "^name)
  in
  aux gvs



let write_struct_info file name typ_vars fields structs =
  fprintf file "%s%c" name '\x00'; write_typ_vars file typ_vars ; fprintf file "%c" (Char.chr (List.length fields)) ;
  let rec aux fs =
    match fs with
    | [] -> ()
    | (lock,ty,_)::t -> write_type_info file lock ty structs ; aux t
  in
  aux fields

let write_structs file structs =
  write_word file (Int64.of_int (List.length structs)) ;
  let rec aux strs =
    match strs with
    | [] -> ()
    | (name,typ_vars,fields)::t -> write_struct_info file name typ_vars fields structs ; aux t
  in
  aux structs






let rec find_label l labels =
  match labels with
  | [] -> None
  | (n,a)::t -> if (String.equal n l) then Some a else find_label l t

let rec write_program_parts f pp labels =
  match pp with
  | [] -> ()
  | h::t -> match h with
    | Instruction i -> (
      fprintf f "%c" (Char.chr i);
      write_program_parts f t labels
    )
    | FullInstruction (i, v) -> (
      fprintf f "%c" (Char.chr i);
      let () = match v with
      | C_Int i -> write_word f (Int64.of_int i)
      in
      write_program_parts f t labels
    )
    | ByteInstruction (i, v) -> (
      fprintf f "%c" (Char.chr i);
      let () = match v with
      | C_Bool b -> fprintf f "%c" (if b then (Char.chr 1) else (Char.chr 0))
      | C_Char c -> fprintf f "%c" (c)
      in
      write_program_parts f t labels
    )
    | LabelInstruction (i, l) -> (
      fprintf f "%c" (Char.chr i);
      let () = match find_label l labels with
      | None -> raise_failure ("Undefined label: " ^ l)
      | Some a -> write_word f (Int64.of_int a)
      in
      write_program_parts f t labels
    )
    | _ -> write_program_parts f t labels

let resolve_place_label program_parts labels =
  let aux pp = match pp with
  | PlaceLabel l -> ( match find_label l labels with
    | None -> raise_failure ("Undefined label: " ^ l)
    | Some a -> translate_single (PlaceFull (C_Int a))
  )
  | p -> p
  in List.map aux program_parts

let write program dest =
  let structs = retrieve_structs program in
  let program_parts = ProgramRep.translate(retrieve_program_parts program) in
  let global_vars = retrieve_global_vars program in
  let labels = retrieve_labels program_parts 0 [] in
  let program_parts = resolve_place_label program_parts labels in
  let output = open_out dest in
  let () = write_structs output structs in
  let () = write_global_vars output global_vars structs in
  let () = write_entry_points output global_vars structs in
  let () = write_program_parts output program_parts labels in
  close_out output