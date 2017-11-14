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

/* explicit sync */
pred_prim NOTIFY{%P}<>;
pred_prim WAIT{%P,%P}<>;
pred_prim NOT{%P}<>;
pred_prim IMPL{%P,%P}<>;

/* special specs */
pred_prim OPEN{%P,%P}<>;
pred_prim OPENED<P,G,c>; //P->peers, G->global prot, c->program channel, root->logical channel
pred_prim EMPTY<c,c,G>;
pred_prim Peer<>; //peer
pred_prim Party{%P}<C>; //%P -> spec,C->bag of channels
pred_prim INITALL<B>;
pred_prim INIT<G>;
pred_prim GLOB{%R}<P,C>; //parties,channels
pred_prim PROJP{%R}<>;  // root->party,   %R->global prot
pred_prim PROJC{%R}<P>; // root->channel, %R->global prot, P->party




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


/* #################################################
      initall({c1..cm}) -> init(c1) * ... init(cm). 
   ################################################# */
lemma_norm  "INIT" self::INITALL<B> & B=union({b},B1) & (b notin B1)-> b::INIT<self> * self::INITALL<B1>.
                                            /*
lemma_norm "INIT1" self::INITALL<B> & B={a}   -> a::INIT<self>.
lemma_norm "INIT2" self::INITALL<B> & B={aa,bb} & aa!=bb -> aa::INIT<self> * bb::INIT<self>.
lemma_norm "INIT3" self::INITALL<B> & B={a,b,c} & a!=b & a!=c & b!=c-> a::INIT<self> * b::INIT<self>* c::INIT<self>.
                                            */

/* ################################################################
    G({P1..Pn},C)  -> Party(P1,C,(G)|P1) * ... * Party(Pn,C,(G)|Pn) 
   ################################################################ */
lemma_norm "SPLIT_GLOB1" self::GLOB{%R}<P,C> & P={A}       
                         -> A::Party{  A::PROJP{%R}<> }<C> * self::INITALL<C>.
lemma_norm "SPLIT_GLOB2" self::GLOB{%R}<P,C> & P={A1,A2} & A1!=A2
                         -> A1::Party{ A1::PROJP{%R}<> }<C> * A2::Party{ A2::PROJP{%R}<> }<C> * self::INITALL<C>.
lemma_norm "SPLIT_GLOB3" self::GLOB{%R}<P,C> & P={A1,A2,A3} & A1!=A2 & A3!=A2 & A1!=A3
                         -> A1::Party{ A1::PROJP{%R}<> }<C> * A2::Party{ A2::PROJP{%R}<> }<C> * A3::Party{ A3::PROJP{%R}<> }<C> * self::INITALL<C>.

/* ##########################################################################
   Party(P,{c1...cm},(G)|P) -> Chan(c1,P,(G)|P,c1) *...* Chan(cm,P,(G)|P,cm) 
   ########################################################################## */
lemma_norm "SPLIT_PROJ1" self::Party{  self::PROJP{%R}<> }<C> & C={c} -> c::Chan{ c::PROJC{%R}<self>}<self>.
lemma_norm "SPLIT_PROJ2" self::Party{  self::PROJP{%R}<> }<C> & C={c1,c2} -> c1::Chan{ c1::PROJC{%R}<self>}<self>* c2::Chan{ c2::PROJC{%R}<self>}<self>.
lemma_norm "SPLIT_PROJ3" self::Party{  self::PROJP{%R}<> }<C> & C={c1,c2,c3} -> c1::Chan{ c1::PROJC{%R}<self>}<self> * c2::Chan{ c2::PROJC{%R}<self>}<self> * c3::Chan{ c3::PROJC{%R}<self>}<self>.


/* #################################################
      initall({c1..cm}) -> init(c1) * ... init(cm). 
   ################################################# */
/*
lemma_norm "INIT1" self::INITALL<B> & B={a}   -> a::INIT<self>.
lemma_norm "INIT2" self::INITALL<B> & B={aa,bb} & aa!=bb -> aa::INIT<self> * bb::INIT<self>.
lemma_norm "INIT3" self::INITALL<B> & B={a,b,c} & a!=b & a!=c & b!=c-> a::INIT<self> * b::INIT<self>* c::INIT<self>.
*/
