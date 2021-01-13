open Eval
open String

let rec char_list_to_string l =
  match l with
  | [] -> ""
  | h :: t -> (Char.escaped h) ^ (char_list_to_string t)

let string_to_char_list s =
  let rec walk s n =
    match n with
    | 0 -> []
    | _ -> (get s ((length s) - n)) :: (walk s (n - 1)) in
    walk s (length s)
  

let rec nat2int n = 
  match n with
  | O    -> 0
  | S n' -> 1 + (nat2int n')

let rec string_of_debruijn t =
  match t with
  | App (t1, t2) -> "App ( " ^ (string_of_debruijn t1) ^ " ) ( " ^ (string_of_debruijn t2) ^ " )"
  | Abs (x, t1)       -> "fun " ^ (char_list_to_string x) ^ " => ( " ^ (string_of_debruijn t1) ^ " )"
  | Var n        -> string_of_int (nat2int n)


let rec string_of_lambda t =
  match t with
  | App0 (t1, t2) -> "App ( " ^ (string_of_lambda t1) ^ " ) ( " ^ (string_of_lambda t2) ^ " )"
  | Abs0 (x, t1)       -> "fun " ^ (char_list_to_string x) ^ " => ( " ^ (string_of_lambda t1) ^ " )"
  | Var0 x        -> char_list_to_string x

let string_option f o =
  match o with
  | Some x -> f x
  | None -> "None"

let option_d_to_lambda ot l =
  match ot with
  | Some t -> debruijn_to_lambda l t
  | None -> None
