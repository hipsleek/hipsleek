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

pred_sess_prot G<C:role,S:role,c:chan> == C->S:c(v#v::msg<1000,2>) ;; C->S:c(v#emp & 1<=v & v<=3);

void C(Channel c)
 requires c::Chan{@S G<C@peer,S,c@chan>}<> *
          c::Common{@S G@all<C,S,c>}<>
 ensures  c::Chan{emp}<> ;
{
 msg m = new msg(1000,2);
 send(c,m);
 send(c,3);
// dprint;
}


void S(Channel c, int reward, int no_players)
 requires c::Chan{@S G<C,S@peer,c@chan>}<> *
          c::Common{@S G@all<C,S,c>}<> & reward>=0
 ensures  c::Chan{emp}<> ;
{
 int fee    = receive(c);
 int option = receive(c);
 if (fee>=1000) { reward = reward + fee; }
 else { reward = 0; }
// dprint;
 assert reward'>=1000;
 assert reward'=0 | reward'>=1000;
// dprint;
}
