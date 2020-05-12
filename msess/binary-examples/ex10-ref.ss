hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

int buyer1(Channel c, int id)
  requires  c::Chan{@S !0;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>=0;
{
  send(c,0)[int];
  int x = receive(c)[int];
  dprint;
  return x;
}


int buyer2(Channel c)
  requires  c::Chan{@S !0;;?1}<>
  ensures   c::Chan{emp}<> & res=1;
{
  send(c,0)[int];
  int x = receive(c)[int];
  return x;
}

int buyer3(Channel c)
  requires  c::Chan{@S !0;;?1}<>
  ensures   c::Chan{emp}<> & res=5;
{
  send(c,0)[int];
  int x = receive(c)[int];
  return x;
}


int buyer4(Channel c,int id)
  requires  c::Chan{@S !0;;?v#v=id}<>
  ensures   c::Chan{emp}<> & res=id;
{
  send(c,0)[int];
  int x = receive(c)[int];
  return x;
}

int buyer5(Channel c)
  requires  c::Chan{@S !0;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  send(c,0)[int];
  int x = receive(c)[int];
  return x;
}


int buyer6(Channel c)
  requires  c::Chan{@S !0;;?ww#ww>0 & ww=a}<>
  ensures   c::Chan{emp}<> & res=a;
{
  dprint;
  send(c,0)[int];
  dprint;
  int x = receive(c)[int];
  dprint;
  return x;
}


int buyer7(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>0}<> & id>0
  ensures   c::Chan{emp}<> & res>0;
{
  send(c,id)[int];
  int x = receive(c)[int];
  return x;
}


int buyer8(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>=0}<> & id>0
  ensures   c::Chan{emp}<> & res>0;
{
  send(c,id)[int];
  int x = receive(c)[int];
  return x;
}


void buyer9(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;!1}<> & id>0
  ensures   c::Chan{@S !1}<>;
{
  send(c,id)[int];
}

int buyer10(Channel c)
  requires  c::Chan{@S !0;;?ww#ww>0&ww=aaa;;!xxx#xxx>0;;?1;;!1;;?7;;!7}<>
  ensures   c::Chan{emp}<> & res=aaa;
{
  send(c,0)[int];
  int x = receive(c)[int];
  send(c,x)[int];
  int y = receive(c)[int];
  send(c,y)[int];
  int z = receive(c)[int];
  send(c,z)[int];
  return x;
}


/*

! l x ⟨l⟩ { l |-> x } . ? ⟨l⟩ { l |-> x + 2 } . end

let (c,c') := new_chan () in
fork { let l := recv(c') in l <- (!l + 2) ; send (c', l) }
send(c,ref 40); !(recv(c))

*/

data intd{
  int val;
}

void P1(Channel c)
  requires  c::Chan{@S ?ww#ww::intd<aaa>;;!ww#ww::intd<aaa+2>}<>
  ensures   c::Chan{emp}<> ;
{
 intd l =  receive(c)[intd];
 l.val = l.val + 2;
 send(c,l)[intd];
}

int P2(Channel c, intd l)
  requires  c::Chan{@S !ww#ww::intd<aaa>;;?ww#ww::intd<aaa+2>}<> * l::intd<40>
  ensures   c::Chan{emp}<> & res=42;
{
 send(c,l)[intd];
 l = receive(c)[intd];
 return l.val;
}


int clientservice(Channel c1, Channel c2)
  requires c1::Chan{@S ?ww#ww::intd<aaa>;;!ww#ww::intd<aaa+2>}<> *
           c2::Chan{@S !ww#ww::intd<aaa>;;?ww#ww::intd<aaa+2>}<>
  ensures  c1::Chan{emp}<> * c2::Chan{emp}<> & res=42;
{
 intd l;
 par{c1,c2}
 {
  case {c1} c1::Chan{@S ?ww#ww::intd<aaa>;;!ww#ww::intd<aaa+2>}<> ->
       intd i =  receive(c1)[intd];
       i.val = i.val + 2;
       send(c1,i)[intd];
  ||
  case {c2} c2::Chan{@S !ww#ww::intd<aaa>;;?ww#ww::intd<aaa+2>}<> ->
       l = new intd(40);
       send(c2,l)[intd];
       l = receive(c2)[intd];
 }
 return l.val;
}
