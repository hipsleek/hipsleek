pred_prim Trans{%P}<sender,receiver>; //trans
pred_prim Sess{%P}<>; //session
pred_prim Chan{%P}<P>; //channel
pred_prim Common{%P}<>;
pred_prim S{-%P}<a@IP>; //send
pred_prim R{+%P}<a@IP>; //receive
pred_prim Seq{%P,%P}<>; //sequence
pred_prim SOr{%P}<>; //disjunction
/*pred_prim Pred{%P}<>; //spred */

/* orders */
pred_prim Event<peer,id:int>; //event
pred_prim HB{%P, %P}<>; //hb
pred_prim CB{%P, %P}<>; //cb

/* protocol lang related */
pred_prim Assume{%P}<>; //assumed
pred_prim Guard{%P}<>; //guard
pred_prim Peer<>; //peer
pred_prim initall<B>;
pred_prim init<c>;

/* explicit sync */
pred_prim NOTIFY{%P}<>;
pred_prim WAIT{%P,%P}<>;
pred_prim NOT{%P}<>;
pred_prim IMPL{%P,%P}<>;

/* special specs */
pred_prim OPEN{%P,%P}<>;
pred_prim INIT<G>;
pred_prim OPENED<c,P,G,c>;
pred_prim EMPTY<c,c,G>;

/* orders relation */
/* need to sync this rel definitions with chr_orders_prelude */
relation oev(int n,int m). //event
relation ohb(int n1,int m1,int n2,int m2). //hb
relation ohbp(int n1,int m1,int n2,int m2). //hbp
relation ocb(int n1,int m1,int n2,int m2). //cb
/* sleek relations */
relation ev(int n). //sevent
relation hb(int n1,int n2). //shb
relation hbp(int n1,int n2). //shbp
relation cb(int n1,int n2). //scb
relation snot_eq(int a,int b).


/* apply A+ before G- */
lemma_norm@0 "A+" self::Chan{@S Assume{%P}<>;;%R}<P> -> self::Chan{@S %R}<P> * %P.
/* to check if * %P is neccessary in the body of this lemma */
lemma_norm@1 "G-" self::Chan{@S Guard{%P}<>;;%R}<P> * %P -> self::Chan{@S %R}<P>.

lemma_norm   "IMPL" self::IMPL{%P, %R}<> * %P -> %R.

/* lemma_.. initall<B> & B={b} union B' => b::init<> *  initall<B'>. */

lemma_norm self::initall<B> & B={a}   -> a::init<self>.
lemma_norm self::initall<B> & B={a,b} -> a::init<self> * b::init<self>. 




