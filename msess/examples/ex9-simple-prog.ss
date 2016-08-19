hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

void buyer1(Channel c, int id)
  requires  c::Chan{@S !0}<this>
  ensures   c::Chan{emp}<this>;
{
  send(c,0);
}


int buyer2(Channel c)
  requires  c::Chan{@S !0;;?1}<this>
  ensures   c::Chan{emp}<this> & res=1;
{
  send(c,0);
  int x = receive(c);
  return x;
}

int buyer3(Channel c)
  requires  c::Chan{@S !0;;?1}<this>
  ensures   c::Chan{emp}<this> & res=5;
{
  send(c,0);
  int x = receive(c);
  return x;
}


int buyer4(Channel c,int id)
  requires  c::Chan{@S !0;;?v#v=id}<this>
  ensures   c::Chan{emp}<this> & res=id;
{
  send(c,0);
  int x = receive(c);
  return x;
}

int buyer5(Channel c)
  requires  c::Chan{@S !0;;?v#v>0}<this>
  ensures   c::Chan{emp}<this> & res>0;
{
  send(c,0);
  int x = receive(c);
  return x;
}


int buyer6(Channel c)
  requires  [a] c::Chan{@S !0;;?ww#ww>0 &a=ww}<this>
  ensures   (exists ww: c:: Chan {emp}< this> & res!=a);
{
  dprint;
  send(c,0);
  dprint;
  int x = receive(c);
  dprint;
  return x;
}

int buyer7(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>0}<this> & id>0
  ensures   c::Chan{emp}<this> & res>0;
{
  send(c,id);
  int x = receive(c);
  return x;
}
 

int buyer8(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;?v#v>=0}<this> & id>0
  ensures   c::Chan{emp}<this> & res>=0;
{
  send(c,id);
  int x = receive(c);
  return x;
}


void buyer9(Channel c, int id)
  requires  c::Chan{@S !v#v>0;;!1}<this> & id>0
  ensures   c::Chan{@S !1}<this>;
{
  send(c,id);
}
