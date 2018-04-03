type 'a editable_string = Cons of (int)*('a array);;

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
let concat (s1: char editable_string) (s2: char editable_string) = match (s1, s2) with
    | (Cons(n1, m1), Cons(n2, m2)) -> Cons(n1, Array.append m1 m2);;

(* reverse : 'a editable_string -> 'a editable_string *)
let reverse s = match s with 
    | Cons(n, m) -> Cons(0, Array.of_list (List.rev (Array.to_list m)));;

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

let alphabet=["1"; "2"; "a"; "b"; "c"; "A"];;

let nil = create "";;

lgh (nil);;
lgh (create("a"));;
lgh (create("abc"));;
lgh (create("12"));;

nonempty nil;;
nonempty (create("a"));;
nonempty (create("12"));;

(* let one = create("1");; *)

concat nil nil;;
concat (nil) (create("a"));;
concat (create("1")) (nil);;
concat (create("1A")) (create("abc"));;

reverse nil;;
reverse (create("abc"));;
reverse (create("12"));;

(* first nil;; *)
first (create("a"));;
first (create("abc"));;

(* last nil;; *)
last (create("a"));;
last (create("abc"));;

let editable = create "abac12a2aAac211";;

let ed_ref = ref editable;;
ed_ref := forward editable;;
ed_ref := back editable;;
ed_ref := moveTo editable 10;;
(* replace editable "b";; *)