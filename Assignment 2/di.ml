type exp = 
  | Cons of int 
  | Abs of exp
  | Ident of string 
  | Add of (exp)*(exp) 
  | Sub of (exp)*(exp) 
  | Mul of (exp)*(exp)
  | Div of (exp)*(exp)
  | Mod of (exp)*(exp)
  | Expo of (exp)*(exp)
  | Boolean of bool
  | Not of exp
  | And of (exp)*(exp)
  | Or of (exp)*(exp)
  | Imply of (exp)*(exp)
  | Eq of (exp)*(exp)
  | Lt of (exp)*(exp)
  | Gt of (exp)*(exp)
  | Le of (exp)*(exp)
  | Ge of (exp)*(exp)
  | Ntuple of (int)*(exp list)
  | Proj of (exp)*(int)*(exp list);;

type ans = 
  | Const of int
  | Bool of bool
  | Tuple of (int)*(ans list);;

type opcode =
  | CONS of int
  | ABS
  | LOOKUP of string 
  | ADD 
  | SUB 
  | MUL
  | DIV
  | MOD
  | EXPO
  | BOOL of bool
  | NOT
  | AND
  | OR
  | IMPLY
  | EQ
  | LT
  | GT
  | LE
  | GE
  | NTUP
  | PROJ;;

let rec power (a, b) = match (a, b) with
  | (l, 0) -> 1
  | (l, 1) -> l
  | (l, k) -> 
    if k mod 2==0 
    then power(l*l, k/2)
    else l*power(l*l, k/2);;

let rec map f l = match l with
  | [] -> []
  | l::ls -> f l :: map f ls;;

let rec map2 f l = match l with
  | [] -> []
  | l::ls -> f l @ map2 f ls;;

exception EmptyStack;;

let rec extract_first (n, l, r) = match (n, l, r) with 
  | (0, ll, rr) -> (ll, rr)
  | (n1, ll::lls, rr) -> extract_first(n1-1, lls, ll::rr)
  | (_, [], _) -> raise EmptyStack;;

let rec eval rho e = match e with
  | Cons i -> Const i
  | Abs e1 -> 
    if eval rho e1 > Const 0
    then eval rho e1
    else eval rho (Mul(e1, Cons(-1)))
  | Ident s1 -> rho s1
  | Add (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(i3+i4))
  | Sub (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(i3-i4))
  | Mul (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(i3*i4))
  | Div (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(i3/i4))
  | Mod (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(i3 mod i4))
  | Expo (e1, e2) -> (match (eval rho e1,eval rho e2) with (Const(i3), Const(i4)) -> Const(power(i3, i4)))
  | Boolean b -> Bool b
  | Not e1 -> (match eval rho e1 with Bool b -> Bool(not b) )
  | And (e1, e2) -> (match (eval rho e1, eval rho e2) with (Bool(i3), Bool(i4)) -> Bool(i3 && i4))
  | Or (e1, e2) -> (match (eval rho e1, eval rho e2) with (Bool(i3), Bool(i4)) -> Bool(i3 || i4))
  | Imply (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Bool true, Bool false) -> Bool false
    | _ -> Bool true)
  | Eq (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Const i1, Const i2) -> Bool (i1==i2)
    |(Bool b1, Bool b2) -> Bool (b1==b2 ))
  | Lt (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Const i1, Const i2) -> Bool (i1<i2))
  | Gt (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Const i1, Const i2) -> Bool (i1>i2))
  | Ge (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Const i1, Const i2) -> Bool (i1>=i2))
  | Le (e1, e2) -> (match (eval rho e1, eval rho e2) with 
    |(Const i1, Const i2) -> Bool (i1<=i2))
  | Ntuple (i, el) -> Tuple(i ,map (eval rho) el)
  | Proj (e1, i, el) -> (match (eval rho e1, i, map (eval rho) el) with 
    |(Const(i1), i2, t1) -> List.nth t1 i1);;

let rec compile e = match e with
  | Cons i -> [CONS(i)]
  | Abs e1 -> compile(e1) @ [ABS]
  | Ident s -> [LOOKUP(s)]
  | Add (e1, e2) -> compile(e1) @ compile(e2) @ [ADD]
  | Sub (e1, e2) -> compile(e1) @ compile(e2) @ [SUB]
  | Mul (e1, e2) -> compile(e1) @ compile(e2) @ [MUL]
  | Div (e1, e2) -> compile(e1) @ compile(e2) @ [DIV]
  | Mod (e1, e2) -> compile(e1) @ compile (e2) @ [MOD]
  | Expo (e1, e2) -> compile(e1) @ compile (e2) @ [EXPO]
  | Boolean b -> [BOOL(b)]
  | Not b -> compile(b) @ [NOT]
  | And (e1, e2) -> compile(e1) @ compile (e2) @ [AND]
  | Or (e1, e2) -> compile(e1) @ compile (e2) @ [OR]
  | Imply (e1, e2) -> compile(e1) @ compile (e2) @ [IMPLY]
  | Eq (e1, e2) -> compile(e1) @ compile (e2) @ [EQ]
  | Lt (e1, e2) -> compile(e1) @ compile (e2) @ [LT]
  | Gt (e1, e2) -> compile(e1) @ compile (e2) @ [GT]
  | Ge (e1, e2) -> compile(e1) @ compile (e2) @ [GE]
  | Le (e1, e2) -> compile(e1) @ compile (e2) @ [LE]
  | Ntuple (i, el) -> map2 compile el @ [CONS(i)] @ [NTUP]
  | Proj (e1, n, el) -> map2 compile el @ [CONS(n)] @ compile e1 @ [PROJ];;

let rec execute ((stack: ans list) , rho, (oplist: opcode list)): ans = match (stack, oplist) with
  | (s ,[]) -> List.hd s
  | (s, CONS(i1)::ops) -> execute(Const(i1)::s, rho, ops)
  | (Const(i1)::s, ABS::ops) -> if i1<0 then execute(Const(-i1)::s, rho, ops) else execute(Const(i1)::s, rho, ops)
  | (s, LOOKUP(str)::ops) -> execute(rho(str)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, ADD::ops) -> execute(Const(i1+i2)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, SUB::ops) -> execute(Const(i2-i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, MUL::ops) -> execute(Const(i1*i2)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, DIV::ops) -> execute(Const(i2/i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, MOD::ops) -> execute(Const(i2 mod i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, EXPO::ops) -> execute(Const(power(i2, i1))::s, rho, ops)
  | (s, BOOL(b)::ops) -> execute(Bool(b)::s, rho, ops)
  | (Bool(b)::s, NOT::ops) -> execute(Bool(not b)::s, rho, ops)
  | (Bool(b1)::Bool(b2)::s, AND::ops) -> execute(Bool(b1 && b2)::s, rho, ops)
  | (Bool(b1)::Bool(b2)::s, OR::ops) -> execute(Bool(b1 || b2)::s, rho, ops)
  | (Bool(b1)::Bool(b2)::s, IMPLY::ops) -> 
    (match (b1, b2) with (false, true) -> execute(Bool(false)::s, rho, ops)
    | _ -> execute(Bool(true)::s, rho, ops))
  | (Const(i1)::Const(i2)::s, EQ::ops) -> execute(Bool(i1==i2)::s, rho, ops)
  | (Bool(i1)::Bool(i2)::s, EQ::ops) -> execute(Bool(i1==i2)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, LT::ops) -> execute(Bool(i2<i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, GT::ops) -> execute(Bool(i2>i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, GE::ops) -> execute(Bool(i2>=i1)::s, rho, ops)
  | (Const(i1)::Const(i2)::s, LE::ops) -> execute(Bool(i2<=i1)::s, rho, ops)
  | (Const(i)::s, NTUP::ops) -> (match extract_first (i, s, []) with 
    |(ll,rr) -> execute(Tuple(i, (rr))::ll, rho, ops))
  | (Const(i)::Const(n)::s, PROJ::ops) -> (match extract_first (n, s, []) with 
    |(l1, r1) -> execute((List.nth (r1) (i))::l1, rho, ops));;

(* example 0 *)
(* let rho0 s = match s with "x" -> Bool(true) | "y" -> Const(3);; 

let e0 = Proj(Cons(1), 3, [Not(And(Boolean(false), Ident("x"))); Abs(Mul(Ident("y"), Cons(-1))); Cons(2)]);;
let c0 = compile(e0);;
let eval_val0 = eval rho0 e0;;
let exec_val0 = execute([], rho0, c0);;

(* example 1 *)
let rho1 s = match s with "x" -> Bool(false) | "y" -> Const(4);; 

let e1 = Ntuple(3, [Not(Or(Boolean(true), Ident("x"))); Abs(Expo(Ident("y"), Cons(5))); Imply(Boolean(false), Ident "x")]);;
let c1 = compile(e1);;
let eval_val1 = eval rho1 e1;;
let exec_val1 = execute([], rho1, c1);; *)

let rho7 s = match s with "iden1" -> Const(1) | "iden2" -> Const(2);;

(* eval *)

eval rho7 (Add(Cons(1),Cons(2)));;
eval rho7 (Mul(Cons(6),Cons(6)));;
eval rho7 (Expo(Cons(2),Cons(4)));;
eval rho7 (Div(Cons(6),Cons(3)));;
eval rho7 (Ident("iden1"));;
eval rho7 (Ident("iden2"));;

eval rho7 (Abs(Cons(-1)));;
eval rho7 (Proj(Cons(2),3,[Cons(12);Cons(121);Cons(33)]));;

eval rho7 (Sub(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(1)));;
eval rho7 (Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2)));;

(* eval rho7 (Or(
	Eq(Cons(5),Cons(5)),
	And(Eq(Sub(Cons(2),Cons(1)),Cons(1)),
		Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2))
	)
));; *)

eval rho7 (And(Boolean(true), Boolean(false)));;
eval rho7 (Imply(Not(Imply(Or(Boolean(true), Boolean(false)), And(Boolean(true), Boolean(false)))),Imply(And(Boolean(true), Boolean(false)), Or(Boolean(true), Boolean(false)))));;

eval rho7 ((Ge(Cons(4),Cons(2))));;
eval rho7 ((Le(Cons(4),Cons(2))));;

(* compile *)

((compile (Add(Cons(1),Cons(2)))));;
((compile (Mul(Cons(6),Cons(6)))));;
((compile (Expo(Cons(2),Cons(4)))));;
((compile (Div(Cons(6),Cons(3)))));;
((compile (Ident("iden1"))));;
((compile (Ident("iden2"))));;

((compile (Abs(Cons(-1)))));;
((compile (Proj(Cons(2),3,[Cons(12);Cons(121);Cons(33)]))));;

((compile (Sub(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(1)))));;
((compile (Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2)))));;

(* execute ([], rho7, (compile (Or(
	Eq(Cons(5),Cons(5)),
	And(Eq(Sub(Cons(2),Cons(1)),Cons(1)),
		Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2))
	)
))));; *)

((compile(And(Boolean(true), Boolean(false)))));;
((compile(Imply(Not(Imply(Or(Boolean(true), Boolean(false)), And(Boolean(true), Boolean(false)))),Imply(And(Boolean(true), Boolean(false)), Or(Boolean(true), Boolean(false)))))));;

((compile(Ge(Cons(4),Cons(2)))));;
((compile(Le(Cons(4),Cons(2)))));;

(* execute *)

execute ([], rho7, (compile (Add(Cons(1),Cons(2)))));;
execute ([], rho7, (compile (Mul(Cons(6),Cons(6)))));;
execute ([], rho7, (compile (Expo(Cons(2),Cons(4)))));;
execute ([], rho7, (compile (Div(Cons(6),Cons(3)))));;
execute ([], rho7, (compile (Ident("iden1"))));;
execute ([], rho7, (compile (Ident("iden2"))));;

execute ([], rho7, (compile (Abs(Cons(-1)))));;
execute ([], rho7, (compile (Proj(Cons(2),3,[Cons(12);Cons(121);Cons(33)]))));;

execute ([], rho7, (compile (Sub(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(1)))));;
execute ([], rho7, (compile (Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2)))));;

(* execute ([], rho7, (compile (Or(
	Eq(Cons(5),Cons(5)),
	And(Eq(Sub(Cons(2),Cons(1)),Cons(1)),
		Mod(Proj(Cons(2),3,[Cons(2);Cons(5);Cons(8)]),Cons(2))
	)
))));; *)

execute ([], rho7, (compile(And(Boolean(true), Boolean(false)))));;
execute ([], rho7, (compile(Imply(Not(Imply(Or(Boolean(true), Boolean(false)), And(Boolean(true), Boolean(false)))),Imply(And(Boolean(true), Boolean(false)), Or(Boolean(true), Boolean(false)))))));;

execute ([], rho7, (compile(Ge(Cons(4),Cons(2)))));;
execute ([], rho7, (compile(Le(Cons(4),Cons(2)))));;