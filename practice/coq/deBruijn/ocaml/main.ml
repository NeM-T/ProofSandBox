open Arith
open Print
open Eval

let write t =
  let parse = Parser.toplevel Lexer.main t in
  print_string ((string_of_lambda parse)^ "\n");
  print_string "  =>";
  let index = free_list [] [] parse in
  match removenames index parse with
  | Some t' ->
      print_string ((string_of_debruijn t') ^ "\n");
      print_string "    =>";
      let result = left_eval t' in
      print_string (string_option string_of_debruijn result);
      print_string ( "  =>" ^ (string_option string_of_lambda (option_d_to_lambda result index)) ^ "\n")
  | None -> print_string "None\n"



let rec get () =
  let getin () =
  let lexbuf = Lexing.from_channel stdin in
    write lexbuf; get ()
  in
  try getin ()
  with
      Lexer.Error m  -> print_string m; print_newline(); get() 
    | Parser.Error -> print_string "Parser Error"; print_newline(); get()


let readfile () = 
      let file = Sys.argv.(1) in
      let oc   = open_in file in
      let rec loop () = 
        let rec ww () =
            let line = input_line oc in
            let lexbuf = Lexing.from_string line in 
            write lexbuf; ww ()
          in
          try ww ()
          with
            End_of_file     -> close_in oc
          | Lexer.Error mes -> print_string mes; print_newline(); loop ()
          | Parser.Error    -> print_string "Parser Error"; print_newline(); loop () in
      loop ()

let () =
  match (Array.length Sys.argv) with
    1 -> get ()
  | _ -> readfile ()

