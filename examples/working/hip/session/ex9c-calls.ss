hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* sor for send */
void sor1(Channel c, int id)
/*
  requires  c::Chan{@S !0 or !1 ;; %R}<>
  ensures   c::Chan{@S %R}<>;
*/
  requires  c::Chan{@S !0 or !1 }<>
  ensures   c::Chan{@S emp}<>;
{
  if (id<0) send(c,1)[int];
  else  send(c,0)[int];
  dprint;
}

int sor2(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0}<>
  ensures   c::Chan{@S emp}<> & res>0;
{
  sor1(c,id);
  int x = receive(c)[int];
  return x;
}

int sor3(Channel c, int id)
  requires  c::Chan{@S !0 or !1;;?v#v>0}<>
  ensures   c::Chan{emp}<> & res>0;
{
  sor1(c,id);
  int x = receive(c)[int];
  return x;
}

pred_sess_prot SOR1<C:role,S:role,c:chan> == C->S:c(0) or C->S:c(1);; SOR1<C,S,c>;

/* should  fail? */
void loop1_sor1(Channel c, int id)
  requires  c::Chan{@S SOR1<C@peer,S,c@chan>}<>
  ensures   c::Chan{@S SOR1<C@peer,S,c@chan>}<>;
{
  dprint;
  if (id<0) send(c,1)[int];
  else  send(c,0)[int];
  dprint;
  loop1_sor1(c,id);
  dprint;
}


void loop3_sor1(Channel c, int id)
  requires  c::Chan{@S SOR1<C@peer,S,c@chan>}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1)[int];
  else  send(c,0)[int];
  loop3_sor1(c,id);
}

void loop2_sor1(Channel c, int id)
  requires  c::Chan{@S !0 or !1}<>
  ensures   c::Chan{emp}<>;
{
  if (id<0) send(c,1)[int];
  else  send(c,0)[int];
  loop2_sor1(c,id);
}

pred_sess_tpproj p1<> == !0 or !1;;p1<>;

void loop4_sor1(Channel c, int id)
  requires  c::Chan{@S p1<>}<>
  ensures   c::Chan{emp}<>;
{
  dprint;
  if (id<0) send(c,1)[int];
  else  send(c,0)[int];
  dprint;
  loop4_sor1(c,id);
}
