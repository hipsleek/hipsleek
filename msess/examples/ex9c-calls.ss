hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* sor for send */
void sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<this>
  ensures   c::Chan{@S %R}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
}

int sor2(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0;;%R}<this>
  ensures   c::Chan{@S %R}<this> & res>0;
{
  sor1(c,id);
  int x = receive(c);
  return x;
}

void sor4(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0;;!0;;%R}<this>
  ensures   c::Chan{@S %R}<this>;
{
  sor2(c,id);
  send(c,0);
}

int sor3(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0}<this>
  ensures   c::Chan{emp}<this> & res>0;
{
  sor1(c,id);
  int x = receive(c);
  return x;
}

/* should this fail? */
void loop1_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<this>
  ensures   c::Chan{@S %R}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  dprint;
  //c::Chan{@S %R}<this> |- c::Chan{@S !0 or !1}<this>
  loop1_sor1(c,id);
  dprint;
}

void loop3_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;%R}<this>
  ensures   c::Chan{emp}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop3_sor1(c,id);
}

void loop2_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1}<this>
  ensures   c::Chan{emp}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop2_sor1(c,id);
}

pred_sess_proj p1<> == !0 or !1;;p1<>;

void loop4_sor1(Channel c, int id)
  requires  c::Chan{@S p1<>}<this>
  ensures   c::Chan{emp}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop4_sor1(c,id);
}


void deleg1(Channel c1, Channel c2, int id)
  requires  c1::Chan{@S !v#v::Chan{@S !0}<this>}<this> * c2::Chan{@S !0}<this>
  ensures   c1::Chan{emp}<this>;
{
  dprint;
  sendc(c1,c2);
}

/* void loop4_sor1(Channel c, int id) */
/*   requires  c::Chan{@S p1<>}<this> */
/*   ensures   c::Chan{emp}<this>; */
/* { */
/*   if (id<0) send(c,1); */
/*   else  send(c,0); */
/*   loop4_sor1(c,id); */
/* } */
