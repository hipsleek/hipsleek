hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_prot G<A:role,B:role,C:role,k1:chan> == A->B:k1(1) ;; C->B:k1(3) ;

void A(Channel k1, cond w)
 requires k1::Chan{@S G<A@peer,B,C,k1@chan>}<> * k1::Common{@S G@all<A,B,C,k1>}<>
 ensures  k1::Chan{emp}<>;
{
 dprint;
 send(k1,1);
 assume w::NOTIFY{ w::Guard{emp & oev(A,id_22)}<> }<>;
 dprint;
 notifyAll(w);
 /* assert !(false); */
 dprint;
}

void B(Channel k1)
 requires k1::Chan{@S G<A,B@peer,C,k1@chan>}<> * k1::Common{@S G@all<A,B,C,k1>}<>
 ensures  k1::Chan{emp}<> ;
{
 int x = receive(k1);
 int y = receive(k1);
 dprint;
}

void C(Channel k1, cond w)
 requires k1::Chan{@S G<A,B,C@peer,k1@chan>}<> * k1::Common{@S G@all<A,B,C,k1>}<>
 ensures  k1::Chan{emp}<> ;
{
 /* assume w::WAIT{ oev(C,id_21), w::Assume{ w::IMPL{ oev(C,id_21), ohbp(A,id_22,C,id_21)}<> }<> }<>; */
 assume w::WAIT{ oev(C,id_21), w::IMPL{oev(C,id_21), ohbp(A,id_22,C,id_21)}<> }<>;
 wait(w);
 send(k1,3);
 dprint;
 dprint;
}

