hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

pred_sess_tpproj p1<> == !0 or !1;;p1<>;

void loop4_sor1(Channel c, int id)
  requires  c::Chan{@S p1<>}<this>
  ensures   c::Chan{emp}<this>;
{
  if (id<0) send(c,1);
  else  send(c,0);
  loop4_sor1(c,id);
}
