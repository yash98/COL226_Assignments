type symbol = Sym of (string)*(int)
type signature = Sign of symbol list
type term = Var of string | Node of (symbol)*(term list)

let rec check_sig (signa: signature): bool = 
  let rec check_in_ht ht (l: symbol list): bool =  match l with
    | [] -> true
    | x::xs -> (match x with Sym(s, i) -> 
      if Hashtbl.mem ht s then false 
      else (let z = Hashtbl.add ht s in check_in_ht ht xs))in 
    let rec check_repeation (signa: signature): bool = match signa with 
      | Sign(l) -> let ht = Hashtbl.create(2*List.length(l)) in (match l with l1 -> check_in_ht ht l) in
      let rec check_arity (signa: signature): bool = match signa with 
        | Sign([]) -> true
        | Sign(x::xs) -> (match x with Sym(s, i) -> if i<0 then false else check_arity(Sign(xs))) in 
          (check_arity signa) && (check_repeation signa)

let rec wfterm (signa: signature) (ter: term): bool = try (match ter with
  | Var(st) -> true
  | Node(sy, l) -> (match sy with Sym(st, i) ->
    (match signa with 
    | Sign(sl) ->  
      let eq_term (symb1: symbol): bool = match symb1 with
        | Sym(st1, i1)-> if (st1==st) && (i1==i) then true else false in 
          let founded =  List.find eq_term sl in (match founded with Sym(fSt, fI) -> 
            let ands (b1: bool) (b2: bool): bool = b1 && b2 in
              let rec same_list ((a: signature), (i: int), (l: signature list)):signature list = (match (a, i, l) with 
                | (a1, 0, l1) -> l1
                | (a1, i1, l1) -> same_list(a1, i1-1, l@[a])) in
                  if (fI == List.length l) then (
                    if (fI == 0) then true 
                    else List.fold_left ands true (List.map2 wfterm (same_list(signa, List.length l, [])) l)) 
                  else false))))
  with Not_found -> false