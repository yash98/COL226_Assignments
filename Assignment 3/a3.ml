let sig1 = [Sym("X",0);Sym("Y",0);Sym("f",1);Sym("g",2);Sym("h",3);Sym("*",2)];;
let sig2 = [Sym("X",0);Sym("Y",0);Sym("Z",0);Sym("f",1);Sym("g",2);Sym("f",3);Sym("*",2)];;
let sig3 = [Sym("f",1)];;
let sig4 = [Sym("X",0);Sym("Y",0);Sym("Z",0)];;

let term1 = (Node (Sym("f", 1)[Var (V "X")]));;
let term2 = (Node (Sym("g", 3)[V "X";Node("h",[Node("f",[V "X"]);V "Y"])]));;
let term3 = (Node (Sym("g", 2)[V "X";Node("*",[V "Y";Node ("*",[V "X";V "Y"])])]));;
let term4 = (Node (Sym("g", 2)[V "X";Node("*",[V "Y";V "X"])]));;
let term5 = (Node (Sym("g", 2)[V "Z";Node("*",[V "X";V "Z"])]));;
let term6 = (Node (Sym("g", 2)[V "Z";Node("g",[V "X";V "Z"])]));;
let term7 = (Var (V ("X")));;
let term8 = (Node ("K",[]));;
let term9 = (Node ("X",[]));;
let term10 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y";Node ("X",[])])]));;
let term11 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y";Node ("f",[V "X"])])]));;
let term12 = (Node ("g",[V "Z";Node("*",[V "Z";Node ("*",[V "X";V "Y"])])]));;
let term13 = (Node ("$",[V "P";V"Q"]));;
let term14 = (Node ("$",[Node ("2",[]); Node ("4",[])]));;
let term15 = (Node ("$",[Node ("2",[]); Node ("3",[])]));;

Printf.printf "(1)check_sig sig1 : %B\n" (check_sig sig1);;
Printf.printf "(2)check_sig sig2 : %B\n" (check_sig sig2);;
Printf.printf "(3)check_sig sig3 : %B\n" (check_sig sig3);;
Printf.printf "(4)check_sig sig4 : %B\n\n" (check_sig sig4);;

Printf.printf "(5)wfterm term1 sig1 : %B\n" (wfterm term1 sig1);;
Printf.printf "(6)wfterm term2 sig1 : %B\n" (wfterm term2 sig1);;
Printf.printf "(7)wfterm term7 sig4 : %B\n" (wfterm term7 sig4);;
Printf.printf "(8)wfterm term8 sig4 : %B\n" (wfterm term8 sig4);;
Printf.printf "(9)wfterm term9 sig4 : %B\n\n" (wfterm term9 sig4);;

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


Printf.printf "(31)mgu term14 term13 : ";; (mgu term14 term13);; Printf.printf("\n");;
Printf.printf "(33)mgu term3  term12 : ";; ((mgu term3 term12));; Printf.printf("\n");;
Printf.printf "(34)mgu term12 term3  : ";; ((mgu term12 term3));; Printf.printf("\n\n");;

Printf.printf "(33.1)subst term12 (mgu term3 term12)  : ";; (subst2 term12 (mgu term3 term12));; Printf.printf("\n");;
Printf.printf "(33.2)subst term3  (mgu term3 term12)  : ";; (subst2 term3 (mgu term3 term12));; Printf.printf("\n\n");;

Printf.printf "(34.1)subst term12 (mgu term12 term3)  : ";; (subst2 term12 (mgu term12 term3));; Printf.printf("\n");;
Printf.printf "(34.2)subst term3  (mgu term12 term3)  : ";; (subst2 term3 (mgu term12 term3));; Printf.printf("\n\n");;
