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

// pred_sess_prot G1<C1:role,C2:role,S:role,c1:chan,c2:chan> ==
//          (C1->S:c1(v#CHOICE(v:int)) * C2->S:c2(v#CHOICE(v:int))) ;
         // (S->C1:c(v#v::answ<v:bool>) * S->C2:c(v#v::answ<v:bool>));

pred_sess_prot G<C1:role,C2:role,S:role,c1:chan,c2:chan> ==
         (C1->S:c1(v#emp& 1<=v & v<=3) * C2->S:c2(v#emp & 1<=v & v<=3)) ;;
         (S->C1:c1(v:bool) * S->C2:c2(v:bool));

/* TODO: c1(v:typ) ===> c1(v # emp & v:typ)

v:bool  ---- is parsed as ------> !msg_91#( emp&v:boolean))

*/

//the projection of * looses/adds extra constraints ...
/**
G ==  C1->S:c1(v#emp& 1<=v & v<=3);;fence({C1,S},c1,1) * C2->S:c2(v#emp & 1<=v & v<=3);;fence({C2,S},c2,2) ;
--------------------------------------------------------------------------------------------------------
G ==  C1->S:c1(v#emp& 1<=v & v<=3) * C2->S:c2(v#emp & 1<=v & v<=3) ;

Pr(G,S) = c1?(v#emp& 1<=v & v<=3);;fence({C1,S},c1,1) * c2?(v#emp & 1<=v & v<=3);;fence({C2,S},c2,2)
Pr(G,S,c1) = ?(v#emp& 1<=v & v<=3);;+fence(1) * c2?(v#emp & 1<=v & v<=3);;fence({C2,S},c2,2)

*/

/*
void C(Channel c)
 requires c::Chan{@S G<C1@peer,C1,S,c1@chan,c2>}<>
 ensures  c::Chan{emp}<> ;
{
 msg m = new msg(1000,2);
 dprint;
 send(c,m)[msg];
 send(c,3)[int];
// dprint;
}
*/


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
 dprint;
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
 dprint;
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



// void Test(int x)
// {
//  int t=x;
// }

// void CallTest(bool x)
// {
// Test(x);
// }
