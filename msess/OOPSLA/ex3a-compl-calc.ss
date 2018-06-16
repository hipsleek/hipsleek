hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

relation REQ(int v) == 0<=v & v<=3.
relation ANS(int v) == 0<=v & v<=3.

pred_sess_prot G<C:role,S:role,c:chan> ==
         C->S:c(v#REQ(v)) ;; S->C:c(v#ANS(v));

//client's view
pred_sess_prot GG<C:role,S:role,c:chan,c0:chan> ==
         C->S:c(v#v:Channel & v=c0) ;; G<C,S,c0> ;

//server's view
pred_sess_prot GGG<S:role,c:chan> == exists C,c0:
         C->S:c(v#v::Chan{@S G<C,S@peer,c0@chan>}<> & v=c0) ;; GGG<S,c>;

//client
void C(Channel c, Channel c0)
 requires c::Chan{@S GG<C@peer,_,c@chan,c0>}<> *
          c0::Chan{@S GG<C@peer,_,c,c0@chan>}<>
 ensures  c::Chan{@S emp}<> * c0::Chan{@S emp}<>;
{
 send(c,c0)[Channel];
 send(c0,1)[int];
 int answ = receive(c0)[int];
 dprint;
}

//server
void Server(Channel cc)
 requires cc::Chan{@S GGG<SS@peer,cc@chan>}<>
 ensures  false;
{
 Channel c0 = receive(cc)[Channel];
 int req = receive(c0)[int];
 send(c0,1)[int];
 dprint;
 Server(cc);
}

//efficient server
void S_complex(Channel c)
 requires c::Chan{@S GGG<S@peer,c@chan>}<>
          * @full[c]
 ensures  false;
{
 dprint;
 Channel c0 = receive(c)[Channel];
 dprint;
 par{c,c0'}
 {
  case {c0'} c0'::Chan{@S %R}<> ->
       int req = receive(c0)[int];
        // compute....
       send(c0,1)[int];
  ||
  case {c} c::Chan{@S %R1}<> ->
       S_complex(c);
 }
}
