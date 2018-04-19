lookUp([G|Gs], V, T) :- G = (V, T); lookUp(Gs, V, T).
lookUp([], V, T) :- fail.

hastype(Gamma, V, T) :- lookUp(Gamma, V, T), string(V).

hastype(Gamma, E1, intT) :- integer(E1).
hastype(Gamma, true, boolT).
hastype(Gamma, false, boolT).

hastype(Gamma, nTuple([]), cartesian([])).

hastype(Gamma, nTuple([G|Gs]), cartesian([T|Ts])) :- hastype(Gamma, G, T), hastype(Gamma, nTuple(Gs), cartesian(Ts)).

hastype(Gamma, abs(E1), intT) :- hastype(Gamma, E1, intT).
hastype(Gamma, add(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, sub(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, mul(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, div(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, mod(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, expo(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
    
hastype(Gamma, and(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT).
hastype(Gamma, or(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT).
hastype(Gamma, imply(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT).
hastype(Gamma, neg(E1), boolT) :- hastype(Gamma, E1, boolT).

hastype(Gamma, eq(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, le(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, ge(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, lt(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).
hastype(Gamma, gt(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT).

hastype(Gamma,  equality(E1, E2), boolT) :- hastype(Gamma, E1, T), hastype(Gamma, E2, T).

hastype(Gamma, if_then_else(B, E1, E2), T) :- hastype(Gamma, B, boolT), hastype(Gamma, E1, T), hastype(Gamma, E2, T).

hastype(Gamma, let_in(V, E1, E2), T) :- typeElaborates(Gamma, def(V, E1), Gamma1), hastype(Gamma1, E2, T).
hastype(Gamma, abstract(V, E1), arrow(T1, T2)) :- typeElaborates(Gamma, bind(V, T1), Gamma1), hastype(Gamma1, E1, T2).
hastype(Gamma, abstract(V, E1), arrow(T1, T2)) :- typeVar(Gamma, V, E1, T1), typeElaborates(Gamma, bind(V, T1), Gamma1), hastype(Gamma1, E1, T2).
hastype(Gamma, apply(E1, E2), T) :- hastype(Gamma, E1, arrow(T2 ,T)), hastype(Gamma, E2, T2).

typeElaborates(Gamma, bind(V, T), [(V, T)|Gamma]).
typeElaborates(Gamma, def(V, E), [(V, T)|Gamma]) :- hastype(Gamma, E, T), string(V).
typeElaborates(Gamma, seq(D1, D2), Gamma2) :- typeElaborates(Gamma, D1, Gamma1), typeElaborates(Gamma1, D2, Gamma2).
%correction 
typeElaborates(Gamma, par(def(V1, E1), def(V2, E2)), [G1|G]) :- V1\=V2, typeElaborates(Gamma, D1, [G1|Gs1]), typeElaborates(Gamma, D2, G).
%correction no cummulation
typeElaborates(Gamma, local(D1, D2), [G2]) :- typeElaborates(Gamma, D1, [G1|Gs1]), typeElaborates([G1|Gs1], D2, [G2|Gs2]).



% typeVar(Gamma, V1, abs(E), intT) :- V1 = E; typeVar(Gamma, V1, E, intT).
% typeVar(Gamma, V1, add(E1, E2), intT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, sub(E1, E2), intT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, mul(E1, E2), intT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, div(E1, E2), intT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, expo(E1, E2), intT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).

% typeVar(Gamma, V1, neg(E), boolT) :- V1 = E; typeVar(Gamma, V1, E, boolT).
% typeVar(Gamma, V1, and(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, or(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, imply(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).

% typeVar(Gamma, V1, eq(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, le(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, ge(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, gt(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).
% typeVar(Gamma, V1, lt(E1, E2), boolT) :- (V1 = E1; V1 = E2); (typeVar(Gamma, V1, E1, intT); typeVar(Gamma, V1, E2, intT)).

% typeVar(Gamma, V1, equality(E1, E2), T) :-((V1 = E1, (hastype(Gamma, E2, T); (typeVar(Gamma, V1, E2, T2), typeElaborates(Gamma, bind(V1, T2), Gamma2), hastype(Gamma2, E2, T))); 
%                                             (V1 = E2, (hastype(Gamma, E1, T); (typeVar(Gamma, V1, E1, T1), typeElaborates(Gamma, bind(V1, T1), Gamma1), hastype(Gamma1, E1, T)));
%                                             (V1 = E1, V1 = E2)))).

% typeVar(Gamma, V, if_then_else(B, E1, E2), boolT) :- V = B.
% typeVar(Gamma, V1, if_then_else(B, E1, E2), T) :- ((V1 = E1, (hastype(Gamma, E2, T); (typeVar(Gamma, V1, E2, T2), typeElaborates(Gamma, bind(V1, T2), Gamma2), hastype(Gamma2, E2, T))); 
%                                                     (V1 = E2, (hastype(Gamma, E1, T); (typeVar(Gamma, V1, E1, T1), typeElaborates(Gamma, bind(V1, T1), Gamma1), hastype(Gamma1, E1, T)));
%                                                     (V1 = E1, V1 = E2)))).

% typeVar(Gamma, V1, let_in(V2, E1, E2), T) :- (V1 = V2); 
%                                             (V1 = E1, (hastype(Gamma, E2, T); (typeVar(Gamma, V1, E2, T2), typeElaborates(Gamma, bind(V1, T2), Gamma2), hastype(Gamma2, E2, T))); 
%                                             (V1 = E2, (hastype(Gamma, E1, T); (typeVar(Gamma, V1, E1, T1), typeElaborates(Gamma, bind(V1, T1), Gamma1), hastype(Gamma1, E1, T))).

% hastype([("X", boolT)], equality("X", 7), T).
% typeElaborates([], seq(def("X", add(3, 6)), def("Y", add("X", 3))), Gamma2).
% hastype([], let_in("X", add(6, 3), add("X", 3)), T).
% hastype([], abstract("X", add("X", 3)), T).
% hastype([], abstract("X", let_in("X", 3, "X")), T).
% hastype([], apply(abstract("X", let_in("X", 3, "X")), 3), T).
% typeElaborates([("X", intT)], seq(bind("X", boolT), def("Y", if_then_else("X", 1, 3))), G).
% typeElaborates([("X", intT)], seq(bind("X", intT), def("Y", if_then_else("X", 1, 3))), G).
% typeElaborates([("X", intT)], par(bind("X", boolT), def("Y", if_then_else("X", 1, 3))), G).
% typeElaborates([("X", intT)], local(bind("X", boolT), def("Y", if_then_else("X", 1, 3))), G).
% hastype([], nTuple([true, 3, nTuple([3, false]), abstract("X", let_in("X", 3, "X"))]), T).
