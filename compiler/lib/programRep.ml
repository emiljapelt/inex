
type byte_container =
  | C_Bool of bool
  | C_Char of char

type full_container =
  | C_Int of int
  
type program =
  | Program of (string * char list * (var_mod * typ * string) list) list * (access_mod * var_mod * typ option * int * string) list * concrete_program_part list

and program_part =
  | Label of string
  | PlaceLabel of string
  | Instruction of int
  | FullInstruction of int * full_container
  | ByteInstruction of int * byte_container
  | LabelInstruction of int * string

and typ =
  | T_Int
  | T_Bool
  | T_Char
  | T_Array of typ option
  | T_Struct of string * typ option list
  | T_Null
  | T_Generic of char
  | T_Routine of char list * (var_mod * typ option) list

and op_typ =
  | NOp_T of typ
  | BinOp_T of string * op_typ * op_typ
  | UnOp_T of string * op_typ
  | TernaryOp_T of op_typ * op_typ * op_typ

and var_mod =
  | Open
  | Stable
  | Const

and access_mod =
  | Internal
  | External
  | Entry

and concrete_program_part =
  | CLabel of string
  | CHalt
  | CStop
  | CPlaceLabel of string
  | Call
  | GoTo of string
  | IfTrue of string
  | PlaceByte of byte_container
  | PlaceFull of full_container
  | CloneFull
  | CloneHalf
  | CloneShort
  | CloneByte
  | FetchFull
  | FetchHalf
  | FetchShort
  | FetchByte
  | FieldFetch
  | DeclareFull
  | DeclareHalf
  | DeclareShort
  | DeclareByte
  | DeclareStruct
  | WriteFull
  | WriteHalf
  | WriteShort
  | WriteByte
  | AssignFull
  | AssignHalf
  | AssignShort
  | AssignByte
  | RefAssign
  | FieldAssign
  | IntAdd
  | IntMul
  | IntSub
  | IntDiv
  | IntMod
  | FullEq
  | IntLt
  | BoolEq
  | BoolNot
  | BoolAnd
  | BoolOr
  | GetSP
  | GetBP
  | ModSP of int
  | FreeVar
  | FreeVars of int
  | PrintInt
  | PrintBool
  | StackFetch of int
  | BPFetch of int
  | SizeOf
  | Start
  | RefFetch
  | IncrRef
  | PrintChar
  | GetInput of int
  | HalfEq
  | ShortEq
  | ByteEq

let rec type_string ty = match ty with
  | T_Int -> "int"
  | T_Bool -> "bool"
  | T_Char -> "char"
  | T_Array None -> "?[]"
  | T_Array Some ty -> type_string ty ^"[]"
  | T_Struct(n,_) -> n
  | T_Null -> "null"
  | T_Generic c -> String.make 1 c
  | T_Routine([],args) -> "("^ (List.map (fun (_,ty_opt) -> Option.fold ~none:"_" ~some:(fun ty -> type_string ty) ty_opt) args |> String.concat ",") ^")"
  | T_Routine(tvs,args) -> "<"^ (List.map (String.make 1) tvs |> String.concat ",") ^">" ^ (type_string (T_Routine([], args)))

let type_index ty = match ty with
  | T_Int -> 0
  | T_Bool -> 1
  | T_Char -> 2
  | T_Array _ -> 3
  | T_Struct _ -> 4
  | T_Generic _ -> 5
  | T_Routine _ -> 6
  | T_Null -> failwith "typing a null"

let type_input_index ty = match ty with
  | T_Int -> 0
  | T_Bool -> 1
  | T_Char -> 2
  | T_Array (Some T_Char) -> 3
  | _ -> failwith "Not an inputable type"

let translate_single c = match c with
    | CLabel (s) -> Label(s)
    | CHalt -> Instruction(0)
    | CStop -> Instruction(1)
    | CPlaceLabel (s) -> PlaceLabel(s)
    | Call -> Instruction(2)
    | GoTo (s) -> LabelInstruction(3, s)
    | IfTrue (s) -> LabelInstruction(4, s)
    | PlaceByte (b) -> ByteInstruction(5, b)
    | PlaceFull (i) -> FullInstruction(6, i)
    | CloneFull -> Instruction(7)
    | CloneHalf -> Instruction(8)
    | CloneShort -> Instruction(9)
    | CloneByte -> Instruction(10)
    | FetchFull -> Instruction(11)
    | FetchHalf -> Instruction(12)
    | FetchShort -> Instruction(13)
    | FetchByte -> Instruction(14)
    | FieldFetch -> Instruction(15)
    | DeclareFull -> Instruction(16)
    | DeclareHalf -> Instruction(17)
    | DeclareShort -> Instruction(18)
    | DeclareByte -> Instruction(19)
    | DeclareStruct -> Instruction(20)
    | WriteFull -> Instruction(21)
    | WriteHalf -> Instruction(22)
    | WriteShort -> Instruction(23)
    | WriteByte -> Instruction(24)
    | AssignFull -> Instruction(25)
    | AssignHalf -> Instruction(26)
    | AssignShort -> Instruction(27)
    | AssignByte -> Instruction(28)
    | RefAssign -> Instruction(29)
    | FieldAssign -> Instruction(31)
    | IntAdd -> Instruction(32)
    | IntMul -> Instruction(33)
    | IntSub -> Instruction(34)
    | IntDiv -> Instruction(35)
    | IntMod -> Instruction(36)
    | FullEq -> Instruction(37)
    | IntLt -> Instruction(38)
    | BoolEq -> Instruction(39)
    | BoolNot -> Instruction(40)
    | BoolAnd -> Instruction(41)
    | BoolOr -> Instruction(42)
    | GetSP -> Instruction(43)
    | GetBP -> Instruction(44)
    | ModSP (i) -> FullInstruction(45, C_Int i)
    | FreeVar -> Instruction(46)
    | FreeVars (i) -> FullInstruction(47, C_Int i)
    | PrintInt -> Instruction(48)
    | PrintBool -> Instruction(49)
    | StackFetch (i) -> FullInstruction(50, C_Int i)
    | BPFetch (i) -> FullInstruction(51, C_Int i)
    | SizeOf -> Instruction(52)
    | Start -> Instruction(53)
    | RefFetch -> Instruction(54)
    | IncrRef -> Instruction(55)
    | PrintChar -> Instruction(56)
    | GetInput (i) -> FullInstruction(57, C_Int i)
    | HalfEq -> Instruction(58)
    | ShortEq -> Instruction(59)
    | ByteEq -> Instruction(60)

let translate concrete_list =
  let rec aux cl acc =
  match cl with
  | [] -> List.rev acc
  | h::t -> aux t (translate_single h :: acc)
  in aux concrete_list []
