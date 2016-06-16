data node {int info; node next;}
data Channel{int info;}

pred_prim Sess{%P}<>;
pred_prim Chan<s:Sess>;

p1<c,s> == c::Chan<s>*s::Sess{msg=1}<>.



void test1(Channel c)
  /* requires c::Chan<s>*s::Sess{emp}<> */
  requires x::p1<c,s>
  ensures  c::Chan<s>*s::Sess{msg=1}<>;
{
  int x;
  x = 1;
}
