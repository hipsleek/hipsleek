hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_prot G<A:role,B:role,C:role,k:chan> == A->B:k(1) ;; B->C:k(2);

void A(Channel k)
 requires k::Chan{@S G2<A,B,C@peer,k@chan>}<>
 ensures  k::Chan{emp}<>;
{
 send(k,1);
}
