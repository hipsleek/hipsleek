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
