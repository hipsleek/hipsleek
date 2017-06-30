hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_prot G<A:role,B:role,C:role,k:chan> == A->B:k(1) ;; B->C:k(2);
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


//lemma_norm self::Common{@S Assume{%P}<>}<> -> %P. 

void A(Channel k)
 requires k::Chan{@S G<A@peer,B,C,k@chan>}<> * k::Common{@S G@all<A,B,C,k>}<>
 ensures  k::Chan{emp}<>;
{
 send(k,1);
 dprint;
}


void B(Channel k)
 requires k::Chan{@S G<A,B@peer,C,k@chan>}<>
 ensures  k::Chan{emp}<>;
{
 int x = receive(k);
 send(k,2);
 dprint;
}

void C(Channel k)
 requires k::Chan{@S G<A,B,C@peer,k@chan>}<>
 ensures  k::Chan{emp}<>;
{
 int x = receive(k);
 dprint;
}
