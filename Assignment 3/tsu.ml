type symbol = Sym of (string)*(int)
type signature = Sign of symbol list
type variable = Var of string
type term = V of variable | Node of (symbol)*(term list)

let rec check_sig (signa: signature): bool = 
  let rec check_in_ht ht (l: symbol list): bool =  match l with
    | [] -> true
    | x::xs -> (match x with Sym(s, i) -> 
      if Hashtbl.mem ht s then false 
      else (let z = Hashtbl.add (ht) (s) (0) in check_in_ht ht xs))in 
    let rec check_repeation (signa: signature): bool = match signa with 
      | Sign(l) -> let ht = Hashtbl.create(2*List.length(l)) in (match l with l1 -> check_in_ht ht l) in
      let rec check_arity (signa: signature): bool = match signa with 
        | Sign([]) -> true
        | Sign(x::xs) -> (match x with Sym(s, i) -> if i<0 then false else check_arity(Sign(xs))) in 
          (check_arity signa) && (check_repeation signa);;

let rec wfterm (signa: signature) (ter: term): bool = try (match ter with
  | V(vr) -> true
  | Node(sy, l) -> (match sy with Sym(st, i) ->
    (match signa with 
    | Sign(sl) ->  
      let eq_term (symb1: symbol): bool = match symb1 with
        | Sym(st1, i1)-> if (st1=st) && (i1=i) then true else false in 
          let founded =  List.find eq_term sl in (match founded with Sym(fSt, fI) -> 
            let ands (b1: bool) (b2: bool): bool = b1 && b2 in
              let rec same_list ((a: signature), (i: int), (l: signature list)):signature list = (match (a, i, l) with 
                | (a1, 0, l1) -> l1
                | (a1, i1, l1) -> same_list(a1, i1-1, l1@[a1])) in
                  let leng = List.length l in
                    if (fI = leng) then (
                      if (fI = 0) then true 
                      else List.fold_left ands true (List.map2 wfterm (same_list(signa, leng, [])) l)) 
                    else false))))
  with Not_found -> false;;

let rec ht (ter: term): int = match ter with
  | V(vr) -> 0
  | Node(sy, []) -> 0
  | Node(sy, l) -> let greater (a: int) (b: int): int = if a>b then a else b in 
    1 + List.fold_left (greater) (-1) (List.map ht l);;

let rec size (ter: term): int = match ter with 
  | V(vr) -> 1
  | Node(sy, []) -> 1
  | Node(sy, l) -> let adder (a: int) (b: int): int = a+b in
    1 + List.fold_left (adder) (0) (List.map size l);;

let rec vars (ter: term): term list = match ter with 
  | V(vr) -> [V(vr)]
  | Node(sy, []) -> []
  | Node(sy, l) -> let rec appender (tl1: term list) (tl2: term list): term list = (match (tl1, tl2) with 
    | ([], l2) -> l2
    | (tl1_1::tl1_r, l2) -> let equals (t: term): bool = (tl1_1=t) in 
      if List.exists equals l2 then appender tl1_r l2 else appender tl1_r (l2@[tl1_1]) )in
    List.fold_left (appender) ([]) (List.map vars l);;

type substitution = Tbl of (variable, term) Hashtbl.t

let rec subst (su: substitution) (ter: term): term = match su with Tbl(ht) ->
  (match ter with
    | V(vr) -> if Hashtbl.mem (ht) (vr) then Hashtbl.find (ht) (vr) else V(vr)
    | Node(sy, []) -> Node(sy, [])
    | Node(sy, l) -> Node(sy, List.map (subst su) l));;

(* su1[su2] *)
let comp (su1: substitution) (su2: substitution): substitution = match (su1, su2) with 
  | (Tbl(ht1), Tbl(ht2)) -> 
    let nht = Hashtbl.create (2*((Hashtbl.length ht1)+(Hashtbl.length ht2))) in
      let copyHt1 (v1: variable) (t1: term): unit = Hashtbl.add nht v1 t1 in
        let placeHt2 (v2: variable) (t2: term): unit = (match t2 with 
          | V(vr) -> if Hashtbl.mem ht1 vr then 
            let tf = Hashtbl.find ht1 vr in Hashtbl.replace nht v2 tf
            else Hashtbl.replace nht v2 t2
          | Node(_, _) -> Hashtbl.replace nht v2 t2) in
            let c = Hashtbl.iter copyHt1 ht1 in
            let p = Hashtbl.iter placeHt2 ht2 in
            Tbl(nht);;

exception NOT_UNIFIABLE;;

let rec mgu (t1: term) (t2: term): substitution = match (t1, t2) with
  | (V(v1), V(v2)) -> let htvv = Hashtbl.create 2 in 
    let unitvv = Hashtbl.add htvv v1 (V(v2)) in Tbl(htvv)
  | (V(v1), Node(sy, [])) -> let htel = Hashtbl.create 2 in 
    let unitel = Hashtbl.add htel v1 (Node(sy, [])) in Tbl(htel)
  | (Node(sy, []), V(v1)) -> let htel = Hashtbl.create 2 in 
    let unitel = Hashtbl.add htel v1 (Node(sy, [])) in Tbl(htel)
  | (V(v1), Node(sy, l)) -> (match v1 with Var(st1) -> 
    let rec eqVar (v3: term): bool = (match v3 with 
    | V(var3) -> (var3 = v1)
    | _ -> false) in
    if List.exists (eqVar) (vars (Node(sy, l))) then raise NOT_UNIFIABLE
    else let htl = Hashtbl.create 2 in 
    let unitl = Hashtbl.add htl v1 (Node(sy, l)) in Tbl(htl))
  | (Node(sy, l), V(v1)) -> (match v1 with Var(st1) -> 
    let rec eqVar (v3: term): bool = (match v3 with 
    | V(var3) -> (var3 = v1)
    | _ -> false) in
  if List.exists (eqVar) (vars (Node(sy, l))) then raise NOT_UNIFIABLE
  else let htl = Hashtbl.create 2 in 
    let unitl = Hashtbl.add htl v1 (Node(sy, l)) in Tbl(htl))
  | (Node(sy1, l1), Node(sy2, l2)) -> (match (sy1, sy2) with 
  | (Sym(st1, i1), Sym(st2, i2)) -> 
    if (st1=st2) && (i1=i2) && (List.length l1 = List.length l2) 
    then List.fold_left comp (Tbl(Hashtbl.create 1)) (List.map2 mgu l1 l2)
    else raise NOT_UNIFIABLE);;

(* EXAMPLES *)

let fold_sub (s: substitution): (variable*term) list = match s with
  | Tbl(ht) -> 
    let tuplist (a: variable) (b: term) (c: (variable*term) list)  = (a, b)::c in 
      Hashtbl.fold (tuplist) ht [];;

(* right signature
let sig_1_right = Sign([Sym("c", 0); Sym("f",1); Sym("d", 2)]);;
let re_sig_1 = check_sig sig_1_right;;

(* wrong signature *)
let sig_2_wrong = Sign([Sym("c", 0); Sym("f",-1); Sym("d", 2)]);;
let re_sig_2 = check_sig sig_2_wrong;;

(* wrong signature *)
let sig_3_wrong = Sign([Sym("c", 0); Sym("c",-1); Sym("d", 2)]);;
let re_sig_3 = check_sig sig_3_wrong;;

(* right term *)
let term_1_right = Node((Sym("d",2)),[Node(Sym("f",1),[Node(Sym("c",0),[])]);V(Var("h"))]);;
let re_term_1 = wfterm sig_1_right term_1_right;;

(* wrong term *)
let term_2_wrong = Node((Sym("d",1)),[Node(Sym("f",1),[Node(Sym("c",0),[])]);V(Var("h"))]);;
let re_term_2 = wfterm sig_1_right term_2_wrong;;

(* wrong term *)
let term_3_wrong = Node((Sym("d",2)),[Node(Sym("f",1),[Node(Sym("c",0),[])])]);;
let re_term_3 = wfterm sig_1_right term_3_wrong;;

(* ht, size, var *)
let ht1 = ht term_1_right;;
let size1 = size term_1_right;;
let vars1 = vars term_1_right;;

let term_4 = Node((Sym("d",2)),[Node(Sym("d",2),[Node(Sym("d",2),[V(Var("h")); V(Var("i"))])]);V(Var("h"))])

let ht4 = ht term_4;;
let size4 = size term_4;;
let vars4 = vars term_4;;

(* substituteion *)
let hasht1 = Hashtbl.create 10;;
Hashtbl.add hasht1 (Var("a")) (V(Var("z")));;
Hashtbl.add hasht1 (Var("b")) (V(Var("d")));;
Hashtbl.add hasht1 (Var("c")) (V(Var("e")));;

let hasht2 = Hashtbl.create 10;;
Hashtbl.add hasht2 (Var("a")) (V(Var("c")));;
Hashtbl.add hasht2 (Var("b")) (Node(Sym("f",1), [V(Var("f"))]));;
Hashtbl.add hasht2 (Var("l")) (V(Var("m")));;

let s1 = Tbl(hasht1);;
let sl1 = fold_sub s1;;
let s2 = Tbl(hasht2);;
let sl2 = fold_sub s2;;

let s3 = comp s1 s2;;
let sl3 = fold_sub s3;;

(* mgu *)
let t1 = Node((Sym("d",2), [V(Var("x")); V(Var("g"))]));;
let t2 = Node((Sym("d",2), [Node(Sym("f",1), [V(Var("f")); V(Var("y"))]); V(Var("y"))]));;

let mgu12 = fold_sub (mgu (t1) (t2));;

let t3 = Node((Sym("t",3), [V(Var("x")); V(Var("g")); V(Var("y"))]));;
let t4 = Node((Sym("t",3), [Node(Sym("d",2), [V(Var("y")); V(Var("y"))]); V(Var("y")); Node(Sym("c",0),[])]));;

let mgu34 = fold_sub (mgu (t3) (t4));;

let t5 = Node((Sym("t",3), [V(Var("x")); V(Var("g")); V(Var("y"))]));;
let t6 = Node((Sym("t",3), [Node(Sym("d",2), [V(Var("xy")); Node(Sym("d",2), [V(Var("x")); V(Var("y"))])]); V(Var("y")); Node(Sym("c",0),[])]));;

let mgu56 = fold_sub (mgu (t5) (t6));; *)

let sig1 = Sign [Sym("X",0);Sym("Y",0);Sym("f",1);Sym("g",2);Sym("h",3);Sym("*",2)];;
let sig2 = Sign [Sym("X",0);Sym("Y",0);Sym("Z",0);Sym("f",1);Sym("g",2);Sym("f",3);Sym("*",2)];;
let sig3 = Sign [Sym("f",1)];;
let sig4 = Sign [Sym("X",0);Sym("Y",0);Sym("Z",0)];;

let term1 = (Node (Sym("f",1),[V(Var "X")]));;
let term2 = (Node (Sym("g",3),[V(Var "X"); Node(Sym("h",2),[Node(Sym("f",2),[V (Var "X")]);V (Var "Y")])]));;
let term3 = (Node (Sym("g",2),[V(Var "X"); Node(Sym("*",2),[V (Var "Y");Node (Sym("*",2),[V (Var "X");V (Var "Y")])])]));;
let term4 = (Node (Sym("g",2),[V(Var "X"); Node(Sym("*",2),[V (Var "Y");V (Var "X")])]));;
let term5 = (Node (Sym("g",2),[V(Var "Z"); Node(Sym("*",2),[V (Var "X");V (Var "Z")])]));;
let term6 = (Node (Sym("g",2),[V(Var "Z"); Node(Sym("g",2),[V (Var "X");V (Var "Z")])]));;
let term7 = (V (Var "X"));;
let term8 = (Node (Sym ("K",0),[]));;
let term9 = (Node (Sym("X",0),[]));;
let term10 = (Node (Sym("g",2),[V (Var "X");Node(Sym("h",3),[Node(Sym("f",1),[V (Var "X")]);V (Var "Y");Node (Sym("X",0),[])])]));;
let term11 = (Node (Sym("g",2),[V (Var "X");Node(Sym("h",3),[Node(Sym("f",1),[V (Var "X")]);V (Var "Y");Node (Sym("f",1),[V (Var "X")])])]));;
let term12 = (Node (Sym("g",2),[V (Var "Z");Node(Sym("*",2),[V (Var "Z");Node (Sym("*",2),[V (Var "X");V (Var "Y")])])]));;
let term13 = (Node (Sym("$",2),[V (Var "P");V (Var "Q")]));;
let term14 = (Node (Sym("$",2),[Node (Sym("2",0),[]); Node (Sym("4",0),[])]));;
let term15 = (Node (Sym("$",2),[Node (Sym("2",0),[]); Node (Sym("3",0),[])]));;

Printf.printf "(1)check_sig sig1 : %B\n" (check_sig sig1);;
Printf.printf "(2)check_sig sig2 : %B\n" (check_sig sig2);;
Printf.printf "(3)check_sig sig3 : %B\n" (check_sig sig3);;
Printf.printf "(4)check_sig sig4 : %B\n\n" (check_sig sig4);;

Printf.printf "(5)wfterm term1 sig1 : %B\n" (wfterm sig1 term1);;
Printf.printf "(6)wfterm term2 sig1 : %B\n" (wfterm sig1 term2);;
Printf.printf "(7)wfterm term7 sig4 : %B\n" (wfterm sig4 term7);;
Printf.printf "(8)wfterm term8 sig4 : %B\n" (wfterm sig4 term8);;
Printf.printf "(9)wfterm term9 sig4 : %B\n\n" (wfterm sig4 term9);;

Printf.printf "(10)ht term9 : %d\n" (ht term9);;
Printf.printf "(11)ht term7 : %d\n" (ht term7);;
Printf.printf "(12)ht term4 : %d\n" (ht term4);;
Printf.printf "(13)ht term10 : %d\n" (ht term10);;
Printf.printf "(14)ht term11 : %d\n\n" (ht term11);;

Printf.printf "(15)size term9 : %d\n" (size term9);;
Printf.printf "(16)size term7 : %d\n" (size term7);;
Printf.printf "(17)size term4 : %d\n" (size term4);;
Printf.printf "(18)size term10 : %d\n" (size term10);;
Printf.printf "(19)size term11 : %d\n\n" (size term11);;

Printf.printf "(20)vars term9 : ";; (vars term9);; Printf.printf("\n");;
Printf.printf "(21)vars term7 : ";; (vars term7);; Printf.printf("\n");;
Printf.printf "(22)vars term4 : ";; (vars term4);; Printf.printf("\n");;
Printf.printf "(23)vars term10 : ";; (vars term10);; Printf.printf("\n");;
Printf.printf "(24)vars term11 : ";; (vars term11);; Printf.printf("\n\n");;


Printf.printf "(31)mgu term14 term13 : ";; fold_sub (mgu term14 term13);; Printf.printf("\n");;
Printf.printf "(33)mgu term3  term12 : ";; fold_sub ((mgu term3 term12));; Printf.printf("\n");;
Printf.printf "(34)mgu term12 term3  : ";; fold_sub ((mgu term12 term3));; Printf.printf("\n\n");;

Printf.printf "(33.1)subst term12 (mgu term3 term12)  : ";; (subst (mgu term3 term12) term12);; Printf.printf("\n");;
Printf.printf "(33.2)subst term3  (mgu term3 term12)  : ";; (subst (mgu term3 term12) term3);; Printf.printf("\n\n");;

Printf.printf "(34.1)subst term12 (mgu term12 term3)  : ";; (subst (mgu term12 term3) term12);; Printf.printf("\n");;
Printf.printf "(34.2)subst term3  (mgu term12 term3)  : ";; (subst (mgu term12 term3) term3);; Printf.printf("\n\n");;
