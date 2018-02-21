type 'alpha editable_string = Cons of (int)*('alpha array);;

exception Empty;;
exception AtLast;;
exception AtFirst;;
exception TooShort;;

(* lgh : 'a editable_string -> int *)
let lgh s = match s with
    | Cons(n, m) -> Array.length m;;

(* nonempty : 'a editable_string -> bool *)
let nonempty s = match s with
    | Cons(n, [||]) -> false
    | _ -> true;;

(* concat : 'a editable_string -> 'b -> 'a editable_string *)
let concat s1 s2 = match (s1, s1) with
    (Cons(n1, m1), Cons(n2, m2)) -> Cons(n1, Array.append m1 m2);;

(* reverse : 'a editable_string -> 'a editable_string *)
let reverse s = match s with 
    | Cons(n, m) -> Cons(n, Array.of_list (List.rev (Array.to_list m)));;
    Const(i)::s
(* create : string -> char editable_string *)
let create str = Cons (0, Array.init (String.length str) (String.get str));;

(* first : 'a editable_string -> 'a *)
let first s = match s with
    | Cons(n , [||]) -> raise Empty
    | Cons(n, m) -> Array.get m 0;;

(* last : 'a editable_string -> 'a *)
let last s = match s with
    | Cons(n , [||]) -> raise Empty
    | Cons(n, m) -> Array.get m (Array.length m -1);;

(* forward : 'a editable_string -> 'a editable_string *)
let forward s = match s with
    Cons(n, m) -> 
    if (n >= Array.length m) then raise AtLast
    else Cons(n+1, m);;

(* back : 'a editable_string -> 'a editable_string *)
let back s = match s with
    Cons(n, m) -> 
    if (n <= 0) then raise AtFirst
    else Cons(n-1, m);;

(* moveTo : 'a editable_string -> int -> 'a editable_string *)
let moveTo s i = match s with
    Cons(n, m) -> Cons(i, m);;
