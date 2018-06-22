hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/*
./hip msess/OOPSLA/ex3a-compl-calc.ss --sess --ann-vp
*/

relation REQ(int v) == 0<=v & v<=3.
relation ANS(int v) == 0<=v & v<=3.

pred_sess_prot CALC<C:role,S:role,c:chan> ==
         C->S:c(v#REQ(v)) ;; S->C:c(v#ANS(v));

//client's view
pred_sess_prot GG<C:role,S:role,c:chan,c0:chan> ==
         C->S:c(v#v:Channel & v=c0) ;; CALC<C,S,c0> ;

//client's view
pred_sess_prot GC<C:role,S:role,c:chan,c0:chan> ==
         C->S:c(v#v::Chan{@S CALC<C,S@peer,c0@chan>}<> & v=c0) ;; CALC<C,S,c0> ;

//server's view
pred_sess_prot GProt<S:role,c:chan> == exists C,c0:
         C->S:c(v#v::Chan{@S CALC<C,S@peer,c0@chan>}<> & v=c0) ;; GProt<S,c>;

//client
void C(Channel c, Channel c0)
 requires c::Chan{@S GC<C@peer,S,c@chan,c0>}<> *
          c0::Chan{@S GC<C@peer,S,c,c0@chan>}<> * c0::Chan{@S CALC<C,S@peer,c0@chan>}<>
 ensures  c::Chan{@S emp}<> * c0::Chan{@S emp}<>;
{
 dprint;
 send(c,c0)[Channel];
 dprint;
 send(c0,1)[int];
 int answ = receive(c0)[int];
 dprint;
}

//server
void Server(Channel cc)
 requires cc::Chan{@S GProt<SS@peer,cc@chan>}<>
 ensures  false;
{
 Channel c0 = receive(cc)[Channel];
 int req = receive(c0)[int];
 send(c0,1)[int];
// dprint;
 Server(cc);
}

//efficient server
void S_complex(Channel c)
 requires c::Chan{@S GProt<S@peer,c@chan>}<>
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
