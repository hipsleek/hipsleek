hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_prot G<A:role,B:role,C:role,k1:chan,k2:chan> == A->B:k1(1) ;; C->B:k2(2);
/*
backtier: <(A -> A^1 , B -> B^1, C -> C^2) , (k -> #1) >
frontier: <(A -> A^1 , B -> B^2, C -> C^2) , (k -> #2) >

#1
backtier: <(A -> A^1 , B -> B^1, C -> \bot) , (k -> #1) >
frontier: <(A -> A^1 , B -> B^1, C -> \bot) , (k -> #1) >
Assume: #1


#2
backtier: <(A -> \bot , B -> B^2, C -> C^2) , (k -> #2) >
frontier: <(A -> \bot , B -> B^2, C -> C^2) , (k -> #2) >
Assume: #2

#1;;#2
[b#1 ; b#2]backtier: <(A -> A^1 , B -> B^1, C -> C^2) , (k -> #1) >
[f#2 ; f#1]frontier: <(A -> A^1 , B -> B^2, C -> C^2) , (k -> #2) >
Asumptions: [f#1rmap ; b#2rmap]: B^1 <_HB B^2
Guards:     [f#1cmap ; b#2cmap]: k#1 <_HB k#2 == A^1 <_HB B^2 /\ B^1 <_HB C^2
*/


/* lemma_norm self::Common{@S Assume{%P}<>}<> -> %P. */

void A(Channel k1, Channel k2)
 requires k1::Chan{@S G<A@peer,B,C,k1@chan,k2>}<> * k1::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<>;
{
 //assert k1::Common{emp}<>;
 send(k1,1);
 dprint;
 // assert  ohbp(B,id_22,B,id_21) & ocb(B,id_21,C,id_21) & ocb(A,id_22,B,id_22);
}


void B(Channel k1, Channel k2)
 requires k1::Chan{@S G<A,B@peer,C,k1@chan,k2>}<> * k2::Chan{@S G<A,B@peer,C,k1,k2@chan>}<> * k1::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<> * k2::Chan{emp}<>;
{
 int x = receive(k1);
 int y = receive(k2);
// send(k2,2);
 dprint;
}

void B_fail(Channel k1, Channel k2)
 requires k1::Chan{@S G<A,B@peer,C,k1@chan,k2>}<> * k2::Chan{@S G<A,B@peer,C,k1,k2@chan>}<> * k1::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k1::Chan{emp}<> * k2::Chan{emp}<>;
{
 int x = receive(k1);
 send(k2,3);
 dprint;
}


void C(Channel k1, Channel k2)
 requires k2::Chan{@S G<A,B,C@peer,k1,k2@chan>}<> * k2::Common{@S G@all<A,B,C,k1,k2>}<>
 ensures  k2::Chan{emp}<>;
{
// int x = receive(k2);
send(k2,2);
 dprint;
}

