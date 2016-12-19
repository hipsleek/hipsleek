pred_prim Trans@trans{%P}<sender,receiver>;
pred_prim Sess@session{%P}<>;
/* pred_prim Chan@channel<sess:Sess>. */
pred_prim Chan@channel{%P}<>;
pred_prim S@send{-%P}<a@IP>;
pred_prim R@receive{+%P}<a@IP>;
pred_prim Seq@sequence{%P,%P}<>;
pred_prim SOr@disjunction{%P}<>;
/* pred_prim Pred@spred{%P}<>; */
