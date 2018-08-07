/******************/
/*   CALCULATOR   */
/*    (simple)    */
/******************/


hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

relation REQ(int v) == 0<=v & v<=3.
relation ANS(int v) == 0<=v & v<=3.

pred_sess_prot G<C:role,S:role,c:chan> ==
         C->S:c(v#REQ(v)) ;; S->C:c(v#ANS(v));

void C(Channel c)
 requires c::Chan{@S G<C@peer,_,c@chan>}<>
 ensures  c::Chan{emp}<>;
{
 send(c,1)[int];
 int answ = receive(c)[int];
}


void S(Channel c)
 requires c::Chan{@S G<_,S@peer,c@chan>}<>
 ensures  c::Chan{emp}<>;
{
 int req = receive(c)[int];
 // compute....
 send(c,1)[int];
}


pred_sess_prot GR<C:role,S:role,c:chan> ==
         C->S:c(v#v::Chan{@S G<_,S@peer,v@chan>}<>) ;; GR<C,S,c>;

void S_complex(Channel c)
 requires c::Chan{@S GR<_,S@peer,c@chan>}<>
          * @full[c]
 ensures  true;
{
 Channel c0 = receive(c)[Channel];
 dprint;
 int req    = receive(c0)[int];
 // compute....
 dprint;
 par{c,c0'}
 {
  case {c0'} c0'::Chan{@S %R1}<> ->
       send(c0,1)[int];
  ||
  case {c}  c::Chan{@S %R2}<> ->
       S_complex(c);
 }
}
