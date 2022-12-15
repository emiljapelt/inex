type program =
  | Program of (string * (bool * typ * string) list) list * (bool * typ * string) list * program_part list

and program_part =
  | EntryPoint of string * (bool * typ) list
  | Label of string
  | Instruction of int
  | IntInstruction of int * int
  | BoolInstruction of int * bool
  | CharInstruction of int * char
  | LabelInstruction of int * string

and typ =
  | T_Int
  | T_Bool
  | T_Char
  | T_Array of typ
  | T_Struct of string
  | T_Null

let type_index ty =
  match ty with
  | T_Int -> 1
  | T_Bool -> 2
  | T_Char -> 3
  | _ -> -1

type concrete_program_part =
  | CEntryPoint of string * (bool * typ) list
  | CLabel of string
  | CHalt
  | CStop
  | Call of string
  | GoTo of string
  | IfTrue of string
  | PlaceBool of bool
  | PlaceInt of int
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
  | AssignFull
  | AssignHalf
  | AssignShort
  | AssignByte
  | RefAssign
  | FieldAssign
  | IntAdd
  | IntMul
  | IntSub
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
  | PrintVar
  | PrintInt
  | PrintBool
  | StackFetch of int
  | BPFetch of int
  | SizeOf
  | ToStart
  | RefFetch
  | IncrRef
  | PlaceChar of char
  | PrintChar
  | GetInput of int
  | HalfEq
  | ShortEq
  | ByteEq

let translate concrete_list =
  let rec aux cl acc =
  match cl with
  | [] -> List.rev acc
  | h::t -> (
    match h with
    | CEntryPoint (s, tl) -> aux t (EntryPoint(s,tl)::acc)
    | CLabel (s) -> aux t (Label(s)::acc)
    | CHalt -> aux t (Instruction(0)::acc)
    | CStop -> aux t (Instruction(1)::acc)
    | Call (s) -> aux t (LabelInstruction(2, s)::acc)
    | GoTo (s) -> aux t (LabelInstruction(3, s)::acc)
    | IfTrue (s) -> aux t (LabelInstruction(4, s)::acc)
    | PlaceBool (b) -> aux t (BoolInstruction(5, b)::acc)
    | PlaceInt (i) -> aux t (IntInstruction(6, i)::acc)
    | CloneFull -> aux t (Instruction(7)::acc)
    | CloneHalf -> aux t (Instruction(8)::acc)
    | CloneShort -> aux t (Instruction(9)::acc)
    | CloneByte -> aux t (Instruction(10)::acc)
    | FetchFull -> aux t (Instruction(11)::acc)
    | FetchHalf -> aux t (Instruction(12)::acc)
    | FetchShort -> aux t (Instruction(13)::acc)
    | FetchByte -> aux t (Instruction(14)::acc)
    | FieldFetch -> aux t (Instruction(15)::acc)
    | DeclareFull -> aux t (Instruction(16)::acc)
    | DeclareHalf -> aux t (Instruction(17)::acc)
    | DeclareShort -> aux t (Instruction(18)::acc)
    | DeclareByte -> aux t (Instruction(19)::acc)
    | DeclareStruct -> aux t (Instruction(20)::acc)
    | AssignFull -> aux t (Instruction(21)::acc)
    | AssignHalf -> aux t (Instruction(22)::acc)
    | AssignShort -> aux t (Instruction(23)::acc)
    | AssignByte -> aux t (Instruction(24)::acc)
    | RefAssign -> aux t (Instruction(25)::acc)
    | FieldAssign -> aux t (Instruction(26)::acc)
    | IntAdd -> aux t (Instruction(27)::acc)
    | IntMul -> aux t (Instruction(28)::acc)
    | IntSub -> aux t (Instruction(29)::acc)
    | FullEq -> aux t (Instruction(30)::acc)
    | IntLt -> aux t (Instruction(31)::acc)
    | BoolEq -> aux t (Instruction(32)::acc)
    | BoolNot -> aux t (Instruction(33)::acc)
    | BoolAnd -> aux t (Instruction(34)::acc)
    | BoolOr -> aux t (Instruction(35)::acc)
    | GetSP -> aux t (Instruction(36)::acc)
    | GetBP -> aux t (Instruction(37)::acc)
    | ModSP (i) -> aux t (IntInstruction(38, i)::acc)
    | FreeVar -> aux t (Instruction(39)::acc)
    | FreeVars (i) -> aux t (IntInstruction(40, i)::acc)
    | PrintVar -> aux t (Instruction(41)::acc)
    | PrintInt -> aux t (Instruction(42)::acc)
    | PrintBool -> aux t (Instruction(43)::acc)
    | StackFetch (i) -> aux t (IntInstruction(44, i)::acc)
    | BPFetch (i) -> aux t (IntInstruction(45, i)::acc)
    | SizeOf -> aux t (Instruction(46)::acc)
    | ToStart -> aux t (Instruction(47)::acc)
    | RefFetch -> aux t (Instruction(48)::acc)
    | IncrRef -> aux t (Instruction(49)::acc)
    | PlaceChar (c) -> aux t (CharInstruction(50, c)::acc)
    | PrintChar -> aux t (Instruction(51)::acc)
    | GetInput (i) -> aux t (IntInstruction(52, i)::acc)
    | HalfEq -> aux t (Instruction(53)::acc)
    | ShortEq -> aux t (Instruction(54)::acc)
    | ByteEq -> aux t (Instruction(55)::acc)
  )
  in aux concrete_list []