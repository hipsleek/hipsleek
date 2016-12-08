


foo<> == (!1;;!2) or (!3;;!4).
  
  x::Chan{@S foo<>;;!1}<> |- x::Chan{@S (!1;!2;!1) or (!3;;!4;;!1)}<>.



pred_sess_prot G1<A,B,C> == A->B : emp ;; [A, B]:Fa2<22,0.5,qqq>.
pred_sess_prot G2<A,B,C> == A->B : emp ;; [A, B]:Fa2<22,0.5,qqq>.

checkentail ll::Sess{@S G1<A@prim,B,C@sec>}<> |- ll::Sess{@S G2<A@prim,B,C@sec>}<>.
checkentail ll::Sess{@S G1<A1@prim,B1,C1@sec>}<> |- ll::Sess{@S G2<A@prim,B,C@sec>}<>.
