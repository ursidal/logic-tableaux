let list_of_string s =
  let rec aux n l =
    if n<0 
    then l
    else aux (n-1) ((String.sub n 1 s)::l)
  in
  aux (String.length s - 1) []
;;
