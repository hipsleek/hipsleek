hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
/*
prot G = A->B:0.
A: c!0;;
B: c?0;;
/*

void buyer1(Channel c, int id)
  requires  c::Chan{@S !0}<>
  ensures   c::Chan{emp}<>;
{
  send(c,0);
}


int buyer2(Channel c)
  requires  c::Chan{@S !0;;?1}<>
  ensures   c::Chan{emp}<> & res=1;
{
  send(c,0);
  int x = receive(c);
  return x;
}

int buyer3(Channel c)
  requires  c::Chan{@S !0;;?1}<>
  ensures   c::Chan{emp}<> & res=5;
{
  send(c,0);
  int x = receive(c);
  return x;
}


int buyer4(Channel c,int id)
  requires  c::Chan{@S !0;;?v#v=id}<>
  ensures   c::Chan{emp}<> & res=id;
{
  send(c,0);
  int x = receive(c);
  return x;
}

int buyer5(Channel c)
  requires  c::Chan{@S !0;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  send(c,0);
  int x = receive(c);
  return x;
}


int buyer6(Channel c)
  requires  [a] c::Chan{@S !0;;?ww#ww>0 &a=ww}<>
  ensures   (exists ww: c:: Chan {emp}< > & res!=a);
{
  dprint;
  send(c,0);
  dprint;
  int x = receive(c);
  dprint;
  return x;
}

int buyer7(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>0}<> & id>0
  ensures   c::Chan{emp}<> & res>0;
{
  send(c,id);
  int x = receive(c);
  return x;
}
 

int buyer8(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>=0}<> & id>0
  ensures   c::Chan{emp}<> & res>=0;
{
  send(c,id);
  int x = receive(c);
  return x;
}


void buyer9(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;!1}<> & id>0
  ensures   c::Chan{@S !1}<>;
{
  send(c,id);
}
