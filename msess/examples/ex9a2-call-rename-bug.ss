hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


int buyer6(Channel c)
  requires  c::Chan{@S !0;;?ww#ww>0&ww=aaa}<this>
  ensures   c::Chan{emp}<this> & res=aaa;
{
  dprint;
  send(c,0);
  dprint;
  int x = receive(c);
  dprint;
  return x;
}

int test(int id)
  requires id>0
ensures res=a & exists (x : x=a & x=id);
{
  return id;
}
int buyer10(Channel c)
  requires  c::Chan{@S !0;;?ww#ww>0&ww=aaa;;!xxx#xxx>0;;?1;;!1;;?7;;!7}<this>
  ensures   c::Chan{emp}<this> & res=aaa;
{
  dprint;
  send(c,0);
  dprint;
  int x = receive(c);
  send(c,x);
  int y = receive(c);
  send(c,y);
  int z = receive(c);
  send(c,z);
  dprint;
  return x;
}
