{
    open AssemblyParser
    open Exceptions
    let meta_table = Hashtbl.create 10
    let () = List.iter (fun (kwd, tok) -> Hashtbl.add meta_table kwd tok) 
                        [
                            "#",              SECTION_END;
                            "#GLOBAL",        GLOBAL_SECTION;
                            "#PROGRAM",       PROGRAM_SECTION;
                            "#ENTRY",         ENTRY_POINT;
                            "#LABEL",         LABEL;
                        ]
    let instruction_table = Hashtbl.create 53
    let () = List.iter (fun (kwd, tok) -> Hashtbl.add instruction_table kwd tok)
                        [ 
                            "HALT",             HALT;
                            "STOP",             STOP;
                            "CALL",             CALL;
                            "GOTO",             GOTO;
                            "IF_TRUE",          IF_TRUE;
                            "PLACE_BOOL",       PLACE_BOOL;
                            "PLACE_INT",        PLACE_INT;
                            "CLONE_FULL",       CLONE_FULL;
                            "CLONE_HALF",       CLONE_HALF;
                            "CLONE_SHORT",      CLONE_SHORT;
                            "CLONE_BYTE",       CLONE_BYTE;
                            "FETCH_FULL",       FETCH_FULL;
                            "FETCH_HALF",       FETCH_HALF;
                            "FETCH_SHORT",      FETCH_SHORT;
                            "FETCH_BYTE",       FETCH_BYTE;
                            "FIELD_FETCH",      FIELD_FETCH;
                            "DECLARE_FULL",     DECLARE_FULL;
                            "DECLARE_HALF",     DECLARE_HALF;
                            "DECLARE_SHORT",    DECLARE_SHORT;
                            "DECLARE_BYTE",     DECLARE_BYTE;
                            "DECLARE_STRUCT",   DECLARE_STRUCT;
                            "ASSIGN_FULL",      ASSIGN_FULL;
                            "ASSIGN_HALF",      ASSIGN_HALF;
                            "ASSIGN_SHORT",     ASSIGN_SHORT;
                            "ASSIGN_BYTE",      ASSIGN_BYTE;
                            "REF_ASSIGN",       REF_ASSIGN;
                            "FIELD_ASSIGN",     FIELD_ASSIGN;
                            "INT_ADD",          INT_ADD;
                            "INT_MUL",          INT_MUL;
                            "INT_SUB",          INT_SUB;
                            "INT_EQ",           INT_EQ;
                            "INT_LT",           INT_LT;
                            "BOOL_EQ",          BOOL_EQ;
                            "BOOL_NOT",         BOOL_NOT;
                            "BOOL_AND",         BOOL_AND;
                            "BOOL_OR",          BOOL_OR;
                            "GETSP",            GETSP;
                            "GETBP",            GETBP;
                            "MODSP",            MODSP;
                            "FREE_VAR",         FREE_VAR;
                            "FREE_VARS",        FREE_VARS;
                            "PRINT_VAR",        PRINT_VAR;
                            "PRINT_INT",        PRINT_INT;
                            "PRINT_BOOL",       PRINT_BOOL;
                            "STACK_FETCH",      STACK_FETCH;
                            "BP_FETCH",         BP_FETCH;
                            "SIZE_OF",          SIZE_OF;
                            "TO_START",         TO_START;
                            "REF_FETCH",        REF_FETCH;
                            "INCR_REF",         INCR_REF;
                        ]

    let line_num = ref 0
}
rule lex = parse
        [' ' '\t' '\r']                         { lex lexbuf }
    |   '\n'                                    { incr line_num; lex lexbuf }
    |   ['-']?['0'-'9']+ as lxm                 { CST_INT (int_of_string lxm) }
    | "true"                                    { CST_BOOL true }
    | "false"                                   { CST_BOOL false }
    | "INT"                                     { INT }
    | "BOOL"                                    { BOOL }
    |   ['#'] ['A'-'Z'] * as id 
                { try
                    Hashtbl.find meta_table id
                  with Not_found -> syntax_error ("Unknown meta symbol \'" ^ id ^ "\'") !line_num}
    |   ['A'-'Z'] ['A'-'Z' '_' ] * as id
                { try
                    Hashtbl.find instruction_table id
                  with Not_found -> syntax_error ("Unknown instruction \'" ^ id ^ "\'") !line_num }
    |   ['A'-'Z' 'a'-'z' '#'] ['A'-'Z' 'a'-'z' '0'-'9' '_' ] * as name   { NAME name }
    | _                 { syntax_error "Unknown token" !line_num}
    | eof               { EOF }
