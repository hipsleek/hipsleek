hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* sor for send */
void sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<>
  ensures   c::Chan{@S %R}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
}

int sor2(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0;;%R}<>
  ensures   c::Chan{@S %R}<> & res>0;
{
  sor1(c,id);
  int x = receive(c);
  return x;
}

int sor3(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  sor1(c,id);
  int x = receive(c);
  return x;
}

/* should  fail? */
void loop1_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<>
  ensures   c::Chan{@S %R}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  dprint;
  //c::Chan{@S %R}<> |- c::Chan{@S !0 or !1;;%R1}<>
  loop1_sor1(c,id);
  dprint;
}

void loop3_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop3_sor1(c,id);
}

void loop2_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop2_sor1(c,id);
}

pred_sess_proj p1<> == !0 or !1;;p1<>;

void loop4_sor1(Channel c, int id)
  requires  c::Chan{@S p1<>}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop4_sor1(c,id);
}
