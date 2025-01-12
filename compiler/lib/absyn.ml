open ProgramRep

type statement =
    | If of expression * statement * statement
    | While of expression * statement * statement option (* condition, body, incrementer *)
    | Block of statement_or_declaration list
    | Assign of reference * expression
    | Call of reference * typ option list * expression list (* context_alias * routine_name * type_arguments * arguments *)
    | Stop
    | Halt
    | Break
    | Continue
    | Print of expression list

and declaration =
    | TypeDeclaration of var_mod * typ * string
    | AssignDeclaration of var_mod * typ option * string * expression

and statement_or_declaration =
    | Statement of statement * int (*   statement * line_number   *)
    | Declaration of declaration * int (*   declaration * line_number   *)
    
and expression =
    | Reference of reference
    | Value of value
    | Ternary of expression * expression * expression

and reference =
    | OtherContext of string * inner_reference
    | LocalContext of inner_reference
    | Null
    (*| Lift of value*)

and inner_reference =
    | Access of string
    | StructAccess of inner_reference * string
    | ArrayAccess of inner_reference * expression

and value =
    | Binary_op of string * expression * expression
    | Unary_op of string * expression
    | ArraySize of inner_reference
    | GetInput of typ
    | Bool of bool
    | Int of int
    | Char of char
    | NewArray of typ * expression
    | ArrayLiteral of expression list
    | NewStruct of string * typ option list * expression list
    | StructLiteral of expression list
    | AnonRoutine of char list * (var_mod * typ option * string) list * statement

and top_declaration =
    | GlobalDeclaration of access_mod * declaration
    | Struct of string * char list * ((var_mod * typ * string) list)
    | FileReference of string * string (* alias * file_path *)

and file = 
    | File of top_declaration list