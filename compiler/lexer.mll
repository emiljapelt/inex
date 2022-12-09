{
  open Parser
  open Exceptions
  let keyword_table = Hashtbl.create 53
  let () = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
                      [ "int", INT;
                        "bool", BOOL;
                        "char", CHAR;
                        "internal", INTERNAL;
                        "external", EXTERNAL;
                        "struct", STRUCT;
                        "new", NEW;
                        "null", NULL;
                        "locked", LOCKED;
                        "var", VAR;
                        "if", IF;
                        "else", ELSE;
                        "while", WHILE;
                        "until", UNTIL;
                        "for", FOR;
                        "repeat", REPEAT;
                        "stop", STOP;
                        "break", BREAK;
                        "continue", CONTINUE;
                        "halt", HALT;
                        "print", PRINT]

  let line_num = ref 0
  
  let char_of_string s lexbuf = match s with
  | "\'\\n\'" -> '\n'
  | _ when s.[1] = '\\' -> syntax_error ("Unknown escape character: " ^ s) (Lexing.lexeme_start lexbuf)
  | _ -> s.[1]
}
rule lex = parse
        [' ' '\t' '\r']        { lex lexbuf }
    |   '\n'        { incr line_num; lex lexbuf }
    |   ['0'-'9']+ as lxm { CSTINT (int_of_string lxm) }
    |   ''' ['\\']? _ ''' as lxm { CSTCHAR (char_of_string lxm lexbuf) }
    |   "true"            { CSTBOOL true }
    |   "false"           { CSTBOOL false }
    |   ['A'-'Z' 'a'-'z' '''] ['A'-'Z' 'a'-'z' '0'-'9' '_'] * as id
                { try
                    Hashtbl.find keyword_table id
                  with Not_found -> NAME id }
    |   '+'           { PLUS }
    |   '*'           { TIMES }
    |   '-'           { MINUS }
    |   '='           { EQ }
    |   "!="          { NEQ }
    |   "<="          { LTEQ }
    |   "<"           { LT }
    |   ">="          { GTEQ }
    |   ">"           { GT }
    |   "&&"          { LOGIC_AND }
    |   "||"          { LOGIC_OR }
    |   '$'           { VALUE }
    |   '|'           { PIPE }
    |   '!'           { NOT }
    |   ":="          { ASSIGNMENT }
    |   '('           { LPAR }
    |   ')'           { RPAR }
    |   '{'           { LBRACE }
    |   '}'           { RBRACE }
    |   '['           { LBRAKE }
    |   ']'           { RBRAKE }
    |   ','           { COMMA }
    |   '.'           { DOT }
    |   ';'           { SEMI }
    |   ':'           { COLON }
    |   '#'           { HASH }
    |   _             { syntax_error "Unknown token" (Lexing.lexeme_start lexbuf) }
    |   eof           { EOF }
