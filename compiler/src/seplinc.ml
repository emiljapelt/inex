open Seplinclib.AssemblyWriter
open Seplinclib.ToProgramRep
open Str
open Seplinclib.Exceptions

let () = Printexc.record_backtrace true

type input_type =
| SEP
| SEA

let resolve_input () =
  try (
    let input = Sys.argv.(1) in
    if not (Sys.file_exists input) then (Printf.printf "%s\n" input; raise_failure "Input file does not exist")
    else if Str.string_match (regexp {|^\(\.\.?\)?\/\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*[a-zA-Z0-9_-]+\.sep$|}) input 0 then (input, SEP)
    else if Str.string_match (regexp {|^\(\.\.?\)?\/\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*[a-zA-Z0-9_-]+\.sea$|}) input 0 then (input, SEA)
    else raise_failure "Invalid input file extension"
  ) with
  | Invalid_argument _ -> raise_failure "No file given to compile"
  | ex -> raise ex

let resolve_output i =
  try (
    let output = Sys.argv.(2) in
    if Str.string_match (regexp {|^\(\.\.?\)?\/\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*$|}) output 0 then  (* Directory *) (
      output ^ List.hd (String.split_on_char '.' (List.hd (List.rev (String.split_on_char '/' i)))) ^ ".sec"
    )
    else if Str.string_match (regexp {|^\(\.\.?\)?\/\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*[a-zA-Z0-9_-]+\.[a-zA-Z0-9_-]+$|}) output 0 then (* File with extension*) (
      output
    )
    else if Str.string_match (regexp {|^\(\.\.?\)?\/\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*[a-zA-Z0-9_-]+$|}) output 0 then (* File without extension *) (
      output ^ ".sec"
    )
    else raise_failure "Invalid output destination"
  ) with
  | Invalid_argument _ -> "./" ^ List.hd (String.split_on_char '.' (List.hd (List.rev (String.split_on_char '/' i)))) ^ ".sec"
  | ex -> raise ex

let print_line ls l =
  Printf.printf "%i | %s\n" (l+1) (List.nth ls l)

let read_file path =
  let file = open_in path in
  let content = really_input_string (file) (in_channel_length file) in
  let () = close_in_noerr file in
  content
    
  
let () = try (
  let (input, in_type) = resolve_input () in
  let output = resolve_output input in
  match in_type with
  | SEP -> write (compile input (fun file -> Seplinclib.Parser.main (Seplinclib.Lexer.start file) (Lexing.from_string (read_file file)))) output
  | SEA -> write (Seplinclib.AssemblyParser.main (Seplinclib.AssemblyLexer.start input) (Lexing.from_string (read_file input))) output
) with 
| Failure(file_opt, line_opt, expl) -> (
  Printf.printf "%s" expl ;
  if Option.is_some file_opt then (
    Printf.printf " in:\n%s" (Option.get file_opt) ;
    if Option.is_some line_opt then (
      Printf.printf ", line %i: \n" (Option.get line_opt) ;
      let line = Option.get line_opt in
      let lines = String.split_on_char '\n' (read_file (Option.get file_opt)) in
      let printer =  print_line lines in match line with
      | 1 -> printer 0 ; printer 1
      | n when n = (List.length lines)-1 -> printer (n-2) ; printer (n-1)
      | _ ->  printer (line-2) ; printer (line-1) ; printer line
    )
    else Printf.printf "\n" ;
  )
  else Printf.printf "\n" ;
)