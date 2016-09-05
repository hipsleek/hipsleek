hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* sor for send */
void sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
}

/* sor for send */
int sor2(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  if (id<0) send(c,1);
  else  send(c,0);
  int x = receive(c);
  return x;
}

/* sor for receive */
int sor3(Channel c, int id)
  requires  c::Chan{@S (?0;;!7) or (?1;;!9);;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  int y = receive(c);
  if (y==0) send(c,7);
  else send(c,9);
  int x = receive(c);
  return x;
}

/* sor for receive */
int sor4(Channel c, int id)
  requires  c::Chan{@S (?0;;!7) or ?1;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  int y = receive(c);
  if (y==0) send(c,7);
  int x = receive(c);
  return x;
}

/* FAIL - ok */
int sor5(Channel c, int id)
  requires  c::Chan{@S (?0;;!7) or ?1;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  int y = receive(c);
  /* if (y==0) */ send(c,7);
  int x = receive(c);
  return x;
}

/* nested sor */
int sor6(Channel c, int id)
  requires  c::Chan{@S (?2 or ?3);;(?0;;!7) or (?1;;(!2 or !3));;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  int z = receive(c);
  dprint;
  int y = receive(c);
  if (y==0) send(c,7);
  else send(c,z);
  int x = receive(c);
  dprint;
  return x;
}

/* nested sor */
int sor7(Channel c, int id)
  requires  c::Chan{@S (?0;;!7) or (?1;;(!2 or !3));;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  
  int y = receive(c);
  if (y==0) send(c,7);
  else send(c,id);
  int x = receive(c);
  dprint;
  return x;
}

/* nested sor */
void sor8(Channel c, int id)
  requires  c::Chan{@S (?2 or ?3);;(?0;;!7) or (?1;;(!2 or !3));;?v#v>0}<>
  ensures   c::Chan{@S ?w#w>0}<>;
{
  int z = receive(c);
  int y = receive(c);
  if (y==0) send(c,7);
  else send(c,z);
}
