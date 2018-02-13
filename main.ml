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
                 (*| Forall of string * ('a)formula
                 | Exists of string * ('a)formula *)
;;

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
  
type ('a) tableau =
  { expr : ('a) formula;
    expanded : bool;
    closed : bool;
    children : 'a children;
  }
and ('a) children =
  |None
  |One of ('a) tableau
  |Two of ('a) tableau * ('a) tableau

let empty_tab =
  {expr = True;
   closed = false;
   expanded = false;
   children = None;}
                              
let init_tableau premisses conclusion =
  let rec aux tableau l =
    match l with
      [] -> tableau
     |x::tl -> aux (One {expr = x;
                         expanded = false;
                         closed = false;
                         children = tableau})
                 tl
  in
  match aux None ((Not conclusion)::(List.rev premisses)) with
  |None -> failwith "Empty list of premisses and conclusion"
  |One tableau -> tableau
  |_ -> failwith "Unexpected result"
;;

let rec append t child =
  if t.closed
  then t
  else
    match t.children with
    |None -> {t with children = child}
    |One child_tab -> {t with children = One (append child_tab child)}
    |Two (left,right) -> {t with children = Two (append left child,append right child)}
;;

let child_apply f c =
  match c with
  |None -> None
  |One child -> One (f child)
  |Two (left,right) -> Two (f left, f right)
;;


let rec map f t =
  let (nexpr,nexp,nclosed)=f (t.expr,t.expanded,t.closed) in
  {expr = nexpr;
   expanded = nexp;
   closed = nclosed;
   children = child_apply (map f) t.children;
  }
;;

let check_closed t =
  let rec passing acc tab =
    match tab.expr with
    |Atom p -> if List.mem (Not (Atom p)) acc
               then {tab with closed = true}
               else
                 {tab with children = child_apply (passing ((Atom p)::acc)) tab.children}
    |Not (Atom p) -> if List.mem (Atom p) acc
                     then {tab with closed = true}
                     else
                       {tab with children = child_apply (passing ((Not (Atom p))::acc)) tab.children}
    |_ -> {tab with children = child_apply (passing acc) tab.children}
  in
  passing [] t
;;

let rec expand n t =
  if n = 0
  then t
  else  
    if t.expanded
    then {t with children = child_apply (expand n) t.children}
    else
      match t.expr with
      |And (a,b) -> let newchild =
                      One ({empty_tab with expr = a;
                                           children = One ({empty_tab with expr = b})})
                    in
                    append {t with expanded = true} newchild |> expand (n-1)
      |Not(And(a,b)) -> let newchild =
                          Two ({empty_tab with expr = Not(a)},{empty_tab with expr = Not(b)})
                        in
                        append {t with expanded = true} newchild |> expand (n-1)
      |Or (a,b) -> let newchild =
                     Two ({empty_tab with expr = a},{empty_tab with expr = b})
                   in
                   append {t with expanded = true} newchild |> expand (n-1)
      |Not(Or(a,b))-> let newchild =
                        One ({empty_tab with expr = Not(a);
                                             children = One ({empty_tab with expr = Not(b)})})
                      in
                      append {t with expanded = true} newchild |> expand (n-1)
      |Imp(a,b) -> let newchild =
                     Two ({empty_tab with expr = Not(a)},{empty_tab with expr = b})
                   in
                   append {t with expanded = true} newchild |> expand (n-1)
      |Not(Imp(a,b))-> let newchild =
                         One ({empty_tab with expr = a;
                                              children = One ({empty_tab with expr = Not(b)})})
                       in
                       append {t with expanded = true} newchild |> expand (n-1)
      |Iff(a,b) -> let newchild =
                     Two ({empty_tab with expr = a;
                                          children = One ({empty_tab with expr = b})},
                          {empty_tab with expr = Not(a);
                                          children = One ({empty_tab with expr = Not(b)})})
                   in
                   append {t with expanded = true} newchild |> expand (n-1)
      |Not(Iff(a,b)) -> let newchild =
                          Two ({empty_tab with expr = a;
                                               children = One ({empty_tab with expr = Not(b)})},
                               {empty_tab with expr = Not(a);
                                               children = One ({empty_tab with expr = b})})
                        in
                        append {t with expanded = true} newchild |> expand (n-1)
      |_ -> { t with children = child_apply (expand n) t.children}
;;

let rec expand_all t =
    if t.expanded
    then {t with children = child_apply expand_all t.children}
    else
      match t.expr with
      |And (a,b) -> let newchild =
                      One ({empty_tab with expr = a;
                                           children = One ({empty_tab with expr = b})})
                    in
                    append {t with expanded = true} newchild |> expand_all
      |Not(And(a,b)) -> let newchild =
                          Two ({empty_tab with expr = Not(a)},{empty_tab with expr = Not(b)})
                        in
                        append {t with expanded = true} newchild |> expand_all
      |Or (a,b) -> let newchild =
                     Two ({empty_tab with expr = a},{empty_tab with expr = b})
                   in
                   append {t with expanded = true} newchild |> expand_all
      |Not(Or(a,b))-> let newchild =
                        One ({empty_tab with expr = Not(a);
                                             children = One ({empty_tab with expr = Not(b)})})
                      in
                      append {t with expanded = true} newchild |> expand_all
      |Imp(a,b) -> let newchild =
                     Two ({empty_tab with expr = Not(a)},{empty_tab with expr = b})
                   in
                   append {t with expanded = true} newchild |> expand_all
      |Not(Imp(a,b))-> let newchild =
                         One ({empty_tab with expr = a;
                                              children = One ({empty_tab with expr = Not(b)})})
                       in
                       append {t with expanded = true} newchild |> expand_all
      |Iff(a,b) -> let newchild =
                     Two ({empty_tab with expr = a;
                                          children = One ({empty_tab with expr = b})},
                          {empty_tab with expr = Not(a);
                                          children = One ({empty_tab with expr = Not(b)})})
                   in
                   append {t with expanded = true} newchild |> expand_all
      |Not(Iff(a,b)) -> let newchild =
                          Two ({empty_tab with expr = a;
                                               children = One ({empty_tab with expr = Not(b)})},
                               {empty_tab with expr = Not(a);
                                               children = One ({empty_tab with expr = b})})
                        in
                        append {t with expanded = true} newchild |> expand_all
      |_ -> { t with children = child_apply expand_all t.children}
;;


  
let prettyprint ?(closed="") t indent =
  let rec tostring n t =
    let indentation = (String.make n indent) in
    let childstr = match t.children with
      |None -> ""
      |One c -> (tostring (n+1) c)
      |Two (c1,c2) -> (tostring (n+1) c1)^(tostring (n+1) c2)
    in
    let cl = if t.closed then closed else "" in
    indentation^(string_of_exp t.expr)^cl^"\n"^childstr
  in
  print_string (tostring 0 t)
    ;;

