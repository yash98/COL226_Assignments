(*
 * Note: you need to change the following datatype and expressions as per your submitted code
 * Please do the changes before you come for demo.
 *)

datatype exp = Num of int
			| Bool of bool
			| Var of string
			| List of exp list
			| Plus of exp * exp
			| Sub of exp * exp
			| Mult of exp * exp
			| Div of exp * exp
			| Tup of exp list
			| Proj of exp * int
			| Gtr of exp * exp
			| Lsr of exp * exp
			| Eql of exp * exp
			| Ifthenelse of exp * exp * exp
			| Lambda of exp * exp
			| App of exp * exp
			| LetinEnd of exp * exp
			| Assgn of exp * exp
			| Seq of exp list
			| Para of exp list
			| Localinend of exp list * exp
			| Dec of exp list
			| Ctup of closure list
			| At of int
			| Bind of exp
			
			| Restp of exp
			| Tothisp of exp
			| Rests of exp
			| Tothiss of exp
			| Restm of exp
			| Tothism of exp
			| Restd of exp
			| Tothisd of exp
			| Restg of exp
			| Tothisg of exp
			| Restl of exp
			| Tothisl of exp
			| Reste of exp
			| Tothise of exp
			| Ifthn of exp * exp
			| Lets of exp*exp
			and
			closure = ACL of (exp * closure) list * exp



krivine(ACL([(Var("z"),ACL([],Num(3)))],Var("z")),[]);;

krivine(ACL([],Plus(Plus(Num(2),Num(3)),Plus(Num(2),Num(3)))),[]);;

krivine(ACL([(Var("z"),ACL([],Num(3)))],Plus(Num(2),Var("z"))),[]);;

krivine(ACL([],App(Lambda(Var("x"),Plus(Var("x"),Num(1))),Num(2))),[]);;

krivine(ACL([],App(Lambda(Var("x"),Mult(Var("x"),Plus(Var("x"),Num(1)))),Num(2))),[]);;

krivine(ACL([],App(Lambda(Var("x"),App(Lambda(Var("d"),Mult(Var("d"),Num(2))),Num(2))),Num(2))),[]);;

krivine(ACL([],Ifthenelse(Gtr(Num(8),Num(2)),App(Lambda(Var("x"),Div(Var("x"),Num(2))),Num(2)),App(Lambda(Var("x"),Mult(Var("x"),Plus(Var("x"),Num(1)))),Num(2)))),[]);;

krivine(ACL([],Ifthenelse(Gtr(Num(1),Num(2)),App(Lambda(Var("x"),Div(Var("x"),Num(2))),Num(2)),App(Lambda(Var("x"),Mult(Var("x"),Plus(Var("x"),Num(1)))),Num(2)))),[]);;

krivine(ACL([],LetinEnd(Para[Assgn(Var("a"),Num(2))],Plus(Var("a"),Num(20)))),[]);;

krivine(ACL([],LetinEnd(Seq[Assgn(Var("a"),Num(2))],Plus(Var("a"),Num(20)))),[]);;

krivine(ACL([],Proj(Tup([Num(1),Num(2),Num(3)]),2)),[]);;

krivine(ACL([],App(Lambda(Var("x"),LetinEnd(Para[Assgn(Var("a"),Num(2))],Plus(Var("a"),Var("x")))),Num(2))),[]);;


SECD([Proj(Tup([Num(12),Num(121),Num(33)]),2)]);;

SECD([LetinEnd(Para([Assgn(Var("a"),Num(1)),Assgn(Var("b"),Num(2)),Assgn(Var("c"),Num(3))]),Plus(Plus(Var("a"),Var("b")),Mult(Var("c"),Num(2)))),Mult(Num(2),Num(3))]);;

SECD([Ifthenelse(Gtr(Num(4),Num(2)),Plus(Num(1),Num(3)),Sub(Num(1),Num(3)))]);;

SECD([LetinEnd(Dec([Para([Assgn(Var("f"),Bool(false))]),Seq([Assgn(Var("a"),Num(1)),Assgn(Var("b"),Num(2)),Assgn(Var("c"),Num(3))])]),Plus(Plus(Var("a"),Var("b")),Mult(Var("c"),Num(2)))),Mult(Num(2),Num(3))]);;

SECD([App(Lambda(Var("x"),Plus(Var("x"),Num(1))),Num(2))]);;

SECD([App(Lambda(Var("x"),Mult(Var("x"),Plus(Var("x"),Num(1)))),Num(2))]);;

SECD([App(Lambda(Var("x"),App(Lambda(Var("d"),MultVar("d"),Num(2))),Num(2))),Num(2)]);;

SECD([Seq([Assgn(Var("a"),LetinEnd(Para([Assgn(Var("a"),Num(1))]),App(Lambda(Var("x"),Plus(Var("x"),Num(1))),Var("a"))))]),Plus(Var("a"),Num(1))]);

