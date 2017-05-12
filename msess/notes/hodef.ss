pred_prim Trans@trans{%P}<sender,receiver>;
pred_prim Sess@session{%P}<>;
/* pred_prim Chan@channel<sess:Sess>. */
pred_prim Chan@channel{%P}<>;
pred_prim S@send{-%P}<a@IP>;
pred_prim R@receive{+%P}<a@IP>;
pred_prim Seq@sequence{%P,%P}<>;
pred_prim SOr@disjunction{%P}<>;
/* pred_prim Pred@spred{%P}<>; */

/* protocol lang related */
pred_prim Assume@assumed{%P}<>;
pred_prim Guard@guard{%P}<>;
pred_prim Peer@peer{%P}<>;

/* orders relation */
/* need to sync this rel definitions with chr_orders_prelude */
relation ev(int n,int m).
relation hb(int n1,int m1,int n2,int m2).
relation cb(int n1,int m1,int n2,int m2).

/* apply A+ before G- */
lemma_norm@0 "A+" self::Chan{@S Assume{%P}<>;;%R}<> -> self::Chan{@S %R}<> * %P;
lemma_norm@1 "G-" self::Chan{@S Guard{%P}<>;;%R}<> *  %P -> self::Chan{@S %R}<> * %P;
