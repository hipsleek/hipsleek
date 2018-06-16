hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

data player{
  int address;
  int choice;
}

data msg{
  int value;
  int address;
}

relation CHOICE(int v) == 1<=v & v<=3.
pred_prim answ<v>;


pred_sess_prot G<C1:role,C2:role,S:role,c1:chan,c2:chan> ==
         (C1->S:c1(v#emp& 1<=v & v<=3) * C2->S:c2(v#emp & 1<=v & v<=3)) ;;
         (S->C1:c1(v:bool) * S->C2:c2(v:bool));


void C(Channel c)
 requires c::Chan{@S G<C1@peer,_,_,c@chan,_>}<>
 ensures  c::Chan{emp}<>;
{
 send(c,1)[int];
 bool answ = receive(c)[bool];
}


void S1(Channel c1, Channel c2, int reward)
 requires c1::Chan{@S G<C1,C2,S@peer,c1@chan,c2>}<> *
          c2::Chan{@S G<C1,C2,S@peer,c1,c2@chan>}<> & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 send(c1,false)[bool];
 send(c2,true)[bool];
}

void S2(Channel c1, Channel c2, int reward)
 requires c1::Chan{@S G<C1,C2,S@peer,c1@chan,c2>}<> *
          c2::Chan{@S G<C1,C2,S@peer,c1,c2@chan>}<> & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 send(c2,true)[bool];
 send(c1,false)[bool];
}

void S3(Channel c1, Channel c2, int reward)
 requires c1::Chan{@S G<C1,C2,S@peer,c1@chan,c2>}<> *
          c2::Chan{@S G<C1,C2,S@peer,c1,c2@chan>}<> * @full[c1,c2]
          & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 par{c1,c2}
 {
  case {c1} c1::Chan{@S %R1}<> ->
       send(c1,false)[bool];
  ||
  case {c2} c2::Chan{@S %R2}<> ->
       send(c2,true)[bool];
 }
}

void S4(Channel c1, Channel c2, int reward)
 requires c1::Chan{@S G<C1,C2,S@peer,c1@chan,c2>}<> *
          c2::Chan{@S G<C1,C2,S@peer,c1,c2@chan>}<> * @full[c1,c2]
          & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<>;
{
 int opt1, opt2;
 par{c1,c2,opt1,opt2}
 {
  case {c1,opt1} c1::Chan{@S %R1}<> ->
       opt1 = receive(c1)[int];
  ||
  case {c2,opt2} c2::Chan{@S %R2}<> ->
       opt2 = receive(c2)[int];
 }
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 par{c1,c2}
 {
  case {c1} c1::Chan{@S %R1}<> ->
       send(c1,false)[bool];
  ||
  case {c2} c2::Chan{@S %R2}<> ->
       send(c2,true)[bool];
 }
}


void S_fail1(Channel c1, Channel c2, int reward)
 requires c1::Chan{@S G<C1,C2,S@peer,c1@chan,c2>}<> *
          c2::Chan{@S G<C1,C2,S@peer,c1,c2@chan>}<> & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 send(c1,false)[bool];
 send(c2,4)[int];
 dprint;
}
