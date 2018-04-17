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
 requires c::Chan{@S G<C@peer,S,c@chan>}<>
 ensures  c::Chan{emp}<> ;
{
 msg m = new msg(1000,2);
 dprint;
 send(c,m)[msg];
 send(c,3)[int];
// dprint;
}


void S(Channel c, int reward, int no_players)
 requires c::Chan{@S G<C,S@peer,c@chan>}<> & reward>=0
 ensures  c::Chan{emp}<> ;
{
 msg m      = receive(c)[msg];
 int option = receive(c)[int];
 if (m.value >= 1000) { reward = reward + m.value; }
 else { reward = 0; }
// dprint;
 assert reward'>=1000;
 assert reward'=0 | reward'>=1000;
// dprint;
}
