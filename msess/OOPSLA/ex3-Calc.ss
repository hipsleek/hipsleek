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


void S_complex(Channel c)
 requires c::Chan{@S G<_,S@peer,c@chan>}<>
          * @full[c]
 ensures  c::Chan{emp}<>;
{
 Channel c0 = receive(c)[int];
 int req    = receive(c0)[int];
 // compute....
 dprint;
 par{c}
 {
  case {c} c0::Chan{@S %R}<> ->
       send(c0,1)[int];
  ||
  case {} emp ->
       S_complex(c);
 }
}
