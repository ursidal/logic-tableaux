let explode s =
  let rec aux n l =
    if n<0 
    then l
    else aux (n-1) ((String.sub s n 1)::l)
  in
  aux (String.length s - 1) []
;;


let matches s = let chars = explode s in fun c -> List.mem c chars
;;

let space = matches " \t\n\r"
and punctuation = matches "()[]{},"
and symbolic = matches "~‘!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"
and alphanumeric = matches
"abcdefghijklmnopqrstuvwxyz_’ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
;;

let rec lexwhile prop inp =
  match inp with
    c::cs when prop c -> let tok,rest = lexwhile prop cs in c^tok,rest
  | _ -> "",inp
;;

let rec lex inp =
  match snd(lexwhile space inp) with
    [] -> []
  | c::cs -> let prop = if alphanumeric(c) then alphanumeric
                        else if symbolic(c) then symbolic
                        else fun c -> false in
             let toktl,rest = lexwhile prop cs in
             (c^toktl)::lex rest
;;

type ('a)formula = False
                 | True
                 | Atom of 'a
                 | Not of ('a)formula
                 | And of ('a)formula * ('a)formula
                 | Or of ('a)formula * ('a)formula
                 | Imp of ('a)formula * ('a)formula
                 | Iff of ('a)formula * ('a)formula
                 | Forall of string * ('a)formula
                 | Exists of string * ('a)formula;;

(* expr1 -> expr2|expr1 iff expr2
   expr2 -> expr3|expr2 imp expr3
expr3 -> expr4|expr3 or expr4
expr4 -> expr5|expr4 and expr5
expr5 -> expr6 | neg expr6
expr6 -> (expr1)|atom

 *)

let rec parse_iff i =
  match parse_imp i with
    e1,"<=>"::i1 -> let e2,i2 = parse_iff i1 in Iff(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_imp i =
  match parse_or i with
    e1,"=>"::i1 -> let e2,i2 = parse_imp i1 in Imp(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_or i =
  match parse_and i with
    e1,"\\/"::i1 -> let e2,i2 = parse_or i1 in Or(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_and i =
  match parse_atom i with
    e1,"/\\"::i1 -> let e2,i2 = parse_and i1 in And(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_atom i =
  match i with
    [] -> failwith "Expected an expression at end of input"
  | "("::i1 -> (match parse_iff i1 with
                  e2,")"::i2 -> e2,i2
                | _ -> failwith "Expected closing bracket")
  | "["::i1 -> (match parse_iff i1 with
                  e2,"]"::i2 -> e2,i2
                | _ -> failwith "Expected closing bracket")
  | "~"::i1 -> let e2,i2 = parse_iff i1 in Not(e2),i2
  | tok::i1 -> Atom(tok),i1
;;

                  
let make_parser pfn s =
  let expr,rest = pfn (lex(explode s)) in
  if rest = [] then expr else failwith "Unparsed input";;

let default_parser = make_parser parse_iff
;;

let rec string_of_exp e =
  match e with
  |True -> "⊤"
  | False -> "⊥"
  | Atom p -> p
  | Not (e) -> "¬"^(string_of_exp e)
  | And(e1,e2) -> "("^(string_of_exp e1)^" ∧ "^(string_of_exp e2)^")"
  | Or(e1,e2) -> "("^(string_of_exp e1)^" ∨ "^(string_of_exp e2)^")"
  | Imp(e1,e2) -> "("^(string_of_exp e1)^" ⊃ "^(string_of_exp e2)^")"
  | Iff(e1,e2) -> "("^(string_of_exp e1)^" ≡ "^(string_of_exp e2)^")";;
