hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

void deleg1(Channel c1, Channel c2, int id)
  requires  c1::Chan{@S !v#v::Chan{@S !0}<>}<> * c2::Chan{@S !0}<>
  ensures   c1::Chan{emp}<>;
{
  dprint;
  sendc(c1,c2);
}

