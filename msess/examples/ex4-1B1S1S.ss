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


pred_sess p1<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0);

pred G2B<bs,ms> ==
  bs::Chan<ms> * ms::Sess{self::p1<bs>}<>;
// bs::Chan<ms> * ms::Sess{bs!int;bs?double;(bs!1;bs!Addr;bs?Date or bs!0)}<>;

void buyer(Chan c, int id, Double budget, Addr a)
  requires c::G2B<c,ms>
  ensures  c::Chan<ms> * ms::Sess{emp}<>;
{send(c, id);
 Double price = receive(c);
 if(price <= budget) {
   send(c, 1);
   send(c, a);
   Date sd = receive(c);
 } else send(c, 0);
}


