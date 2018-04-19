type exp = 
  | Lambda of (string)*(exp) 
  | Call of (exp)*(exp) 
  | Let of (string)*(exp)*(exp)
  | If of (exp)*(exp)*(exp)
  | Cons of int 
  | Abs of exp
  | Var of string 
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
  | Bubble

type secd_op = 
  | CLOS of (string)*(secd_op list) 
  | APP 
  | RET 
  | LET 
  | ENDLET  
  | IF            
  | CONS of int
  | ABS
  | VAR of string 
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

type bind = Bcons of (string)*(int) | Bbool of (string)*(bool);;

type ans = 
  | Const of int
  | Bool of bool
  | Lexb of (string)*(bind list)*(secd_op list);;

type dump = Dump of (ans list)*(bind list)*(secd_op list);;

exception Undefined_Expo;;

let rec power (a, b) = match (a, b) with
  | (0, 0) -> raise Undefined_Expo
  | (l, 0) -> 1
  | (l, 1) -> l
  | (l, k) -> 
    if k mod 2==0 
    then power(l*l, k/2)
    else l*power(l*l, k/2);;

let rec compile_secd (e :exp): secd_op list = match e with
  | Lambda(s,e1) -> [CLOS(s,compile_secd(e1)@[RET])]
  | Call(e1,e2) -> compile_secd(e1)@compile_secd(e2)@[APP]
  | Let(s,e1,e2) -> compile_secd(e1)@[LET]@[VAR(s)]@compile_secd(e2)@[ENDLET]
  | If(e1,e2,e3) -> compile_secd(e2)@compile_secd(e3)@compile_secd(e1)@[IF]
  | Cons i -> [CONS(i)]
  | Abs e1 -> compile_secd(e1) @ [ABS]
  | Var s -> [VAR(s)]
  | Add (e1, e2) -> compile_secd(e1) @ compile_secd(e2) @ [ADD]
  | Sub (e1, e2) -> compile_secd(e1) @ compile_secd(e2) @ [SUB]
  | Mul (e1, e2) -> compile_secd(e1) @ compile_secd(e2) @ [MUL]
  | Div (e1, e2) -> compile_secd(e1) @ compile_secd(e2) @ [DIV]
  | Mod (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [MOD]
  | Expo (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [EXPO]
  | Boolean b -> [BOOL(b)]
  | Not b -> compile_secd(b) @ [NOT]
  | And (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [AND]
  | Or (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [OR]
  | Imply (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [IMPLY]
  | Eq (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [EQ]
  | Lt (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [LT]
  | Gt (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [GT]
  | Ge (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [GE]
  | Le (e1, e2) -> compile_secd(e1) @ compile_secd (e2) @ [LE];;

exception UNBOUND;;
exception TYPE_ERROR;;

let rec exec_secd ((s:ans list),(e: bind list),(c: secd_op list),(d: dump list)):(ans list)*(bind list)*(secd_op list)*(dump list)= try (match (s, e, c, d) with
  | (s1, e1, [], d1) -> (s1, e1, [], d1)
  | (s1, e1, CLOS(str,c1)::c2, d1) -> exec_secd(Lexb(str,e1,c1)::s1, e1, c2, d1)
  | (Const(a1)::Lexb(str,e2,c2)::s1, e1, APP::c1, d1) -> exec_secd([], Bcons(str,a1)::e2, c2, Dump(s1,e1,c1)::d1)
  | (Bool(a1)::Lexb(str,e2,c2)::s1, e1, APP::c1, d1) -> exec_secd([], Bbool(str,a1)::e2, c2, Dump(s1,e1,c1)::d1)
  | (a1::s1, e1, RET::c1, Dump(s2,e2,c2)::d1) -> exec_secd(a1::s2, e2, c2, d1)
  | (Const(a1)::s1, e1, LET::VAR(str)::c1, d1) -> exec_secd(s1, Bcons(str, a1)::e1, c1, d1)
  | (Bool(a1)::s1, e1, LET::VAR(str)::c1, d1) -> exec_secd(s1, Bbool(str, a1)::e1, c1, d1)
  | (s1, b1::e1, ENDLET::c1, d1) -> exec_secd(s1, e1, c1, d1)
  | (b1::a2::a1::s1, e1, IF::c1, d1) -> (match b1 with Bool(b) -> 
    if b then exec_secd(a1::s1, e1, c1, d1) else exec_secd(a2::s1, e1, c1, d1)
    | _ -> raise TYPE_ERROR)
  | (s1, e1, CONS(i1)::c1, d1) -> exec_secd(Const(i1)::s1, e1, c1, d1)
  | (Const(i1)::s1, e1, ABS::c1, d1) -> if i1<0 then exec_secd(Const(-i1)::s1, e1, c1, d1) else exec_secd(Const(i1)::s1, e1, c1, d1)
  | (s1, e1, VAR(str)::c1, d1) -> let p(b) = match b with Bcons(s,i) -> (s=str) | Bbool(s,b) -> (s=str) in 
    let v = List.find p e1 in let a1 = match v with Bcons(s,i) -> Const(i) | Bbool(s,b) -> Bool(b)  in
    exec_secd(a1::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, ADD::c1, d1) -> exec_secd(Const(i1+i2)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, SUB::c1, d1) -> exec_secd(Const(i2-i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, MUL::c1, d1) -> exec_secd(Const(i1*i2)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, DIV::c1, d1) -> exec_secd(Const(i2/i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, MOD::c1, d1) -> exec_secd(Const(i2 mod i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, EXPO::c1, d1) -> exec_secd(Const(power(i2, i1))::s1, e1, c1, d1)
  | (s1, e1, BOOL(b)::c1, d1) -> exec_secd(Bool(b)::s1, e1, c1, d1)
  | (Bool(b)::s1, e1, NOT::c1, d1) -> exec_secd(Bool(not b)::s1, e1, c1, d1)
  | (Bool(b1)::Bool(b2)::s1, e1, AND::c1, d1) -> exec_secd(Bool(b1 && b2)::s1, e1, c1, d1)
  | (Bool(b1)::Bool(b2)::s1, e1, OR::c1, d1) -> exec_secd(Bool(b1 || b2)::s1, e1, c1, d1)
  | (Bool(b1)::Bool(b2)::s1, e1, IMPLY::c1, d1) -> 
    (match (b1, b2) with (false, true) -> exec_secd(Bool(false)::s1, e1, c1, d1)
    | _ -> exec_secd(Bool(true)::s1, e1, c1, d1))
  | (Const(i1)::Const(i2)::s1, e1, EQ::c1, d1) -> exec_secd(Bool(i1==i2)::s1, e1, c1, d1)
  | (Bool(i1)::Bool(i2)::s1, e1, EQ::c1, d1) -> exec_secd(Bool(i1==i2)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, LT::c1, d1) -> exec_secd(Bool(i2<i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, GT::c1, d1) -> exec_secd(Bool(i2>i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, GE::c1, d1) -> exec_secd(Bool(i2>=i1)::s1, e1, c1, d1)
  | (Const(i1)::Const(i2)::s1, e1, LE::c1, d1) -> exec_secd(Bool(i2<=i1)::s1, e1, c1, d1)
  ) with Not_found -> raise UNBOUND;;


let execute_secd (c: secd_op list): ans = let al = exec_secd([],[], c, []) in 
  match al with (s, e, c, d) -> List.hd s;;

type clos = C of (exp)*(envblock list)
  and envblock = E of (string)*(clos);;

exception Division_by_zero;;

let rec kriv ((c: clos), (s: clos list)): (clos)*(clos list) = try(match (c, s) with
  | (C(ex, e1), s1) -> (match (ex,s1) with 
    | (Boolean(b), []) -> (C(Boolean(b), e1), [])
    | (Cons(i), []) -> (C(Cons(i), e1), [])

    | (Lambda(st, ex1), c1::s2) -> kriv(C(ex1, E(st, c1)::e1), s2)
    | (Lambda(st, ex1), []) -> (C(Bubble, []), [])

    | (Call(ex1, ex2), s2) -> kriv(C(ex1, e1), C(ex2, e1)::s2)

    | (Let(st, ex1, ex2), s2) -> kriv(C(ex2, E(st, C(ex1 , e1))::e1), s2)

    | (If(ex1, ex2, ex3), s2) -> kriv(C(ex1, e1), C(If(Bubble, ex2, ex3), e1)::s2)
    | (Boolean(b), C(If(Bubble, ex2, ex3), e2)::s2) -> if b then kriv(C(ex2, e2), s2) else kriv(C(ex3, e2), s2)

    | (Abs(ex1), s2) -> kriv(C(ex1, e1), C(Abs(Bubble), e1)::s2)
    | (Cons(c), C(Abs(Bubble), e2)::s2) -> 
      if c<0 then kriv(C(Cons(-c), e2), s2) else kriv(C(Cons(c), e2), s2)

    | (Add(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Add(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Add(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Add(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Add(Cons(c1), Bubble), e2)::s2) -> kriv(C(Cons(c1+c2), e2), s2)

    | (Sub(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Sub(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Sub(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Sub(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Sub(Cons(c1), Bubble), e2)::s2) -> kriv(C(Cons(c1-c2), e2), s2)

    | (Mul(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Mul(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Mul(Bubble, ex2), e2)::s2) -> 
      if c<>0 then kriv(C(ex2, e2), C(Mul(ex, Bubble), e2)::s2) else kriv(C(Cons(0), e2), s2)
    | (Cons(c2), C(Mul(Cons(c1), Bubble), e2)::s2) -> kriv(C(Cons(c1*c2), e2), s2)

    | (Div(ex1, ex2), s2) -> kriv(C(ex2, e1), C(Div(ex1, Bubble), e1)::s2)
    | (Cons(c), C(Div(ex1, Bubble), e2)::s2) -> 
      if c<>0 then kriv(C(ex1, e2), C(Div(Bubble, Cons(c)), e2)::s2) else raise Division_by_zero
    | (Cons(c2), C(Div(Bubble,Cons(c1)), e2)::s2) -> kriv(C(Cons(c2/c1), e2), s2)

    | (Mod(ex1, ex2), s2) -> kriv(C(ex2, e1), C(Mod(ex1, Bubble), e1)::s2)
    | (Cons(c), C(Mod(Bubble, ex2), e2)::s2) -> 
      if c<>1 then kriv(C(ex2, e2), C(Mod(ex, Bubble), e2)::s2) else kriv(C(Cons(0), e2), s2)
    | (Cons(c2), C(Mod(Cons(c1), Bubble), e2)::s2) -> kriv(C(Cons(c1*c2), e2), s2)

    | (Expo(ex1, ex2), s2) -> kriv(C(ex2, e1), C(Expo(ex1, Bubble), e1)::s2)
    | (Cons(c), C(Expo(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Expo(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Expo(Cons(c1), Bubble), e2)::s2) -> kriv(C(Cons(c1*c2), e2), s2)
    
    | (Not(ex1), s2) -> kriv(C(ex1, e1), C(Not(Bubble), e1)::s2)
    | (Boolean(b), C(Not(Bubble), e1)::s2) -> kriv(C(Boolean(not(b)), e1), s2)
    
    | (And(ex1, ex2), s2) -> kriv(C(ex1, e1), C(And(Bubble, ex2), e1)::s2)
    | (Boolean(b), C(And(Bubble, ex2), e2)::s2) -> 
      if b then kriv(C(ex2, e2), C(And(Boolean(b), Bubble),e2)::s2) else kriv(C(Boolean(false), e2), s2)
    | (Boolean(c1), C(And(Boolean(c2), Bubble), e2)::s2) -> kriv(C(Boolean(c1&&c2), e2), s2)
    
    | (Or(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Or(Bubble, ex2), e1)::s2)
    | (Boolean(b), C(Or(Bubble, ex2), e2)::s2) -> 
      if b then kriv(C(Boolean(true), e2), s2) else kriv(C(ex2, e2), C(Or(Boolean(b), Bubble),e2)::s2)
    | (Boolean(c1), C(Or(Boolean(c2), Bubble), e2)::s2) -> kriv(C(Boolean(c1||c2), e2), s2)
    
    | (Imply(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Imply(Bubble, ex2), e1)::s2)
    | (Boolean(b), C(Imply(Bubble, ex2), e2)::s2) -> 
      if b then kriv(C(ex2, e2), C(Imply(Boolean(b), Bubble),e2)::s2) else kriv(C(Boolean(true), e2), s2)
    | (Boolean(c2), C(Imply(Boolean(c1), Bubble), e2)::s2) -> (match (c1, c2) with
      | (true, false) -> kriv(C(Boolean(false), e2), s2)
      | _ -> kriv(C(Boolean(true), e2), s2))
    
    | (Eq(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Eq(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Eq(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Eq(ex, Bubble), e2)::s2)
    | (Boolean(b), C(Eq(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Eq(ex, Bubble), e2)::s2)
    | (Cons(c1), C(Eq(Cons(c2), Bubble), e2)::s2) -> kriv(C(Boolean(c1=c2), e2), s2)
    | (Boolean(c1), C(Eq(Boolean(c2), Bubble), e2)::s2) -> kriv(C(Boolean(c1=c2), e2), s2)
    
    | (Lt(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Lt(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Lt(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Lt(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Lt(Cons(c1), Bubble), e2)::s2) -> kriv(C(Boolean(c1<c2), e2), s2)

    | (Gt(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Gt(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Gt(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Gt(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Gt(Cons(c1), Bubble), e2)::s2) -> kriv(C(Boolean(c1>c2), e2), s2)

    | (Le(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Le(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Le(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Le(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Le(Cons(c1), Bubble), e2)::s2) -> kriv(C(Boolean(c1<=c2), e2), s2)

    | (Ge(ex1, ex2), s2) -> kriv(C(ex1, e1), C(Ge(Bubble, ex2), e1)::s2)
    | (Cons(c), C(Ge(Bubble, ex2), e2)::s2) -> kriv(C(ex2, e2), C(Ge(ex, Bubble), e2)::s2)
    | (Cons(c2), C(Ge(Cons(c1), Bubble), e2)::s2) -> kriv(C(Boolean(c1>=c2), e2), s2)

    | (Var(st), s2) -> let p(eb) = match eb with E(ss, clos) -> (ss=st) in 
    let v = List.find p e1 in let reqclos = match v with E(ss1, clos1) -> clos1  in
    kriv(reqclos, s2))
  ) with Not_found -> raise UNBOUND;;

let execute_kriv (ex: exp): clos = let a =  kriv ((C(ex, [])),[]) in (match a with (cl,s) -> cl);;

kriv(C(Var("z"), [E("z",C(Cons(3),[]))]),[]);;
kriv(C(Add(Add(Cons(2),Cons(3)),Add(Cons(2),Cons(3))), []),[]);;
kriv(C(Add(Cons(2),Var("z")), [E("z",C(Cons(3),[]))]),[]);;
kriv(C(Call(Lambda("x",Add(Var("x"),Cons(1))),Cons(2)),[]),[]);;
kriv(C(Call(Lambda("x",Mul(Var("x"),Add(Var("x"),Cons(1)))),Cons(2)),[]),[]);;
kriv(C(Call(Lambda("x",Call(Lambda("d",Mul(Var("d"),Cons(2))),Cons(2))),Cons(2)),[]),[]);;
kriv(C(If(Gt(Cons(8),Cons(2)),Call(Lambda("x",Div(Var("x"),Cons(2))),Cons(2)),Call(Lambda("x",Mul(Var("x"),Add(Var("x"),Cons(1)))),Cons(2))),[]),[]);;
kriv(C(If(Gt(Cons(1),Cons(2)),Call(Lambda("x",Div(Var("x"),Cons(2))),Cons(2)),Call(Lambda("x",Mul(Var("x"),Add(Var("x"),Cons(1)))),Cons(2))),[]),[]);;
kriv(C(Let("a",Cons(2),Add(Var("a"),Cons(20))),[]),[]);;
kriv(C(Let("a",Cons(2),Add(Var("a"),Cons(20))),[]),[]);;
(* krivine(ACL([],Proj(Tup([Cons(1),Cons(2),Cons(3)]),2)),[]);; *)
kriv(C(Call(Lambda("x",Let("a",Cons(2),Add(Var("a"),Var("x")))),Cons(2)),[]),[]);;

(* SECD([Proj(Tup([Cons(12),Cons(121),Cons(33)]),2)]);; *)
execute_secd(compile_secd(Let("a",Cons(1),Let("b",Cons(2),Let("c",Cons(3),Add(Add(Var("a"),Var("b")),Mul(Var("c"),Cons(2))))))));;
(* execute_secd(compile_secd(Mul(Cons(2),Cons(3))));; *)
execute_secd(compile_secd(If(Gt(Cons(4),Cons(2)),Add(Cons(1),Cons(3)),Sub(Cons(1),Cons(3)))));;
execute_secd(compile_secd(Let("f",Boolean(false),Let("a",Cons(1),Let("b",Cons(2),Let("c",Cons(3), Add(Add(Var("a"),Var("b")),Mul(Var("c"),Cons(2)))))))));;
execute_secd(compile_secd(Call(Lambda("x",Add(Var("x"),Cons(1))),Cons(2))));;
execute_secd(compile_secd(Call(Lambda("x",Mul(Var("x"),Add(Var("x"),Cons(1)))),Cons(2))));;
execute_secd(compile_secd(Let("a",Cons(1),Call(Lambda("x",Add(Var("x"),Cons(1))),Var("a")))));;
execute_secd(compile_secd(Let("a", Cons(1), Add(Var("a"),Cons(1)))));;

let e101 = Lambda("x1",Add(Cons(34),Cons(2)));;
let k12 = execute_kriv(Call(e101,Div(Cons(1),Cons(0))));;
let s12 = execute_secd(compile_secd(Call(e101,Div(Cons(1),Cons(0)))));;
