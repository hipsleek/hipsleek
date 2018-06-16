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

pred_sess_prot G2<C1:role,C2:role,C3:role,S:role,c1:chan,c2:chan,c3:chan> ==
         (C1->S:c1(v#CHOICE(v)) * C2->S:c2(v#CHOICE(v))) ;;
         ((S->C1:c1(v:bool);;S->C3:c3(v:bool)) * S->C2:c2(v:bool));;
         S->C1:c1(v#v=1);


void S21(Channel c1, Channel c2, Channel c3, int reward)
 requires c1::Chan{@S G2<C1,C2,C3,S@peer,c1@chan,c2,c3>}<> *
          c2::Chan{@S G2<C1,C2,C3,S@peer,c1,c2@chan,c3>}<> *
          c3::Chan{@S G2<C1,C2,C3,S@peer,c1,c2,c3@chan>}<> & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<> * c3::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 send(c1,false)[bool];
 send(c2,true)[bool];
 send(c3,true)[bool];
 send(c1,1)[int];
}


void S22(Channel c1, Channel c2, Channel c3, int reward)
 requires c1::Chan{@S G2<C1,C2,C3,S@peer,c1@chan,c2,c3>}<> *
          c2::Chan{@S G2<C1,C2,C3,S@peer,c1,c2@chan,c3>}<> *
          c3::Chan{@S G2<C1,C2,C3,S@peer,c1,c2,c3@chan>}<> & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<> * c3::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 /* .. play .. */
 // if (false) { opt1 = opt2 ;}
 send(c1,false)[bool];
 send(c3,true)[bool];
 send(c2,true)[bool];
 send(c1,1)[int];
}

void S23(Channel c1, Channel c2, Channel c3, int reward)
 requires
          c1::Chan{@S G2<C1,C2,C3,S@peer,c1@chan,c2,c3>}<> *
          c2::Chan{@S G2<C1,C2,C3,S@peer,c1,c2@chan,c3>}<> *
          c3::Chan{@S G2<C1,C2,C3,S@peer,c1,c2,c3@chan>}<>
          * @full[c1,c2,c3]
          & reward>=0
 ensures  c1::Chan{emp}<> * c2::Chan{emp}<> * c3::Chan{emp}<>;
{
 int opt1     = receive(c1)[int];
 int opt2     = receive(c2)[int];
 assert opt1'>=1 & opt1'<=3;
 assert opt2'>=1 & opt2'<=3;
 par{c1,c2,c3}
 {
  case {c1,c3} c1::Chan{@S %R1}<> * c3::Chan{@S %R2}<> ->
       send(c1,false)[bool];
       send(c3,true)[bool];
  ||
  case {c2} c2::Chan{@S %R3}<> ->
       send(c2,true)[bool];
 }
 send(c1,1)[int];
}
