hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

void deleg1(ref Channel c1, ref Channel c2)
  requires  c1::Chan{@S !v#v::Chan{@S !0}<>}<> * c2::Chan{@S !0}<>
  ensures   c1'::Chan{emp}<>;
{
  dprint;
  send(c1,c2)[Channel];
}


Channel deleg2(ref Channel c1)
  requires  c1::Chan{@S ?v#v::Chan{@S !0}<>}<>
  ensures   c1'::Chan{emp}<> * res::Chan{@S !0}<>;
{
  dprint;
  Channel c2 = receive(c1)[Channel];
  /* dprint; */
  /* send(c2,0); */
  return c2;
}

void p1(ref Channel c1, ref Channel c2)
  requires  c1::Chan{@S !v#v::Chan{@S !0}<>}<> * c2::Chan{@S !0}<>
  ensures   c1'::Chan{emp}<>;
{
  deleg1(c1,c2);
}

Channel p2(ref Channel c1)
  requires  c1::Chan {@S ?v#v::Chan{@S !0}<>}<>
  ensures   c1'::Chan{emp}<> * res::Chan{emp}<>;
{
  Channel c2 = deleg2(c1);
  send(c2,0)[int];
  return c2;
}

//FAIL -ok
Channel p2_fail(Channel c1)
  requires  c1::Chan{@S ?v#v::Chan{@S !0}<>}<>
  ensures   c1::Chan{emp}<> * res::Chan{emp}<>;
{
  Channel c2 = deleg2(c1);
  /* send(c2,0); */
  return c2;
}
