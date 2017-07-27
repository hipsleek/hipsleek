hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_prot G<A:role,B:role,C:role,k1:chan,k2:chan> == A->B:k1(1) ;; B->C:k2(2) ;; C->B:k1(3) ;

/* lemma_norm self::Common{@S Assume{%P}<>}<> -> %P. */

void A(Channel k1, Channel k2)
 requires k1::Chan{@S G<A@peer,B,C,k1@chan,k2>}<> * k1::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<>;
{
  dprint;
 send(k1,1);
 dprint;
}


void B(Channel k1, Channel k2)
 requires k1::Chan{@S G<A,B@peer,C,k1@chan,k2>}<> * k2::Chan{@S G<A,B@peer,C,k1,k2@chan>}<> * k1::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<> * k2::Chan{emp}<>;
{
 int x = receive(k1);
 send(k2,2);
 int y = receive(k1);
 dprint;
}

void C(Channel k1, Channel k2)
 requires k1::Chan{@S G<A,B,C@peer,k1@chan,k2>}<> * k2::Chan{@S G<A,B,C@peer,k1,k2@chan>}<> * k2::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<> * k2::Chan{emp}<>;
{
 int x = receive(k2);
 send(k1,3);
 dprint;
}
