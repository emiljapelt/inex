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
    let incr_linenum lexbuf = 
        let pos = lexbuf.Lexing.lex_curr_p in
        lexbuf.Lexing.lex_curr_p <- { pos with
            Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
            Lexing.pos_bol = pos.Lexing.pos_cnum;
        }

    let set_filename filename lexbuf =
        let pos = lexbuf.Lexing.lex_curr_p in
        lexbuf.Lexing.lex_curr_p <- { pos with
            Lexing.pos_fname = filename;
        }
}
rule lex = parse
        [' ' '\t']               { lex lexbuf }
    |   ('\r''\n' | '\n')        { incr_linenum lexbuf ; lex lexbuf }
    |   ['-']?['0'-'9']+ as lxm                 { CST_INT (int_of_string lxm) }
    | "true"                                    { CST_BOOL true }
    | "false"                                   { CST_BOOL false }
    | "INT"                                     { INT }
    | "BOOL"                                    { BOOL }
    |   ['#'] ['A'-'Z'] * as id 
                { try
                    Hashtbl.find meta_table id
                  with Not_found -> raise (Failure (Some((Lexing.lexeme_start_p lexbuf).pos_fname), Some((Lexing.lexeme_start_p lexbuf).pos_lnum), ("Unknown meta symbol \'" ^ id ^ "\'"))) }
    |   ['A'-'Z'] ['A'-'Z' '_' ] * as id
                { try
                    Hashtbl.find instruction_table id
                  with Not_found -> raise (Failure (Some((Lexing.lexeme_start_p lexbuf).pos_fname), Some((Lexing.lexeme_start_p lexbuf).pos_lnum), ("Unknown instruction \'" ^ id ^ "\'"))) }
    |   ['A'-'Z' 'a'-'z' '#'] ['A'-'Z' 'a'-'z' '0'-'9' '_' ] * as name   { NAME name }
    | _                 { raise (Failure (Some((Lexing.lexeme_start_p lexbuf).pos_fname), Some((Lexing.lexeme_start_p lexbuf).pos_lnum), "Unknown token")) }
    | eof               { EOF }

and start filename = parse
    ""  { set_filename filename lexbuf ; lex lexbuf }
