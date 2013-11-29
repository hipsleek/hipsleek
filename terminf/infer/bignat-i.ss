data node {
  int val;
  node next;
}

bigint<> == 
  self = null or
  self::node<p, q> * q::bigint<> & 0 <= p <= 9;

node clone(node x)
  requires x::bigint<>
  ensures x::bigint<> * res::bigint<>;
{
  if (x == null) {
    return x;
  }
  return new node(x.val, clone(x.next));
}

/*
bigint<v> == 
  self = null & v = v0 or
  self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = F(p, v1);

node clone(node x)
  requires x::bigint<v>
  ensures x::bigint<v> * res::bigint<vr> & vr = G(v);
{
  if (x == null) return x;
  return new node(x.val, clone(x.next));
}

x::bigint<v> & x = null 
  -> v = v0 & vr = G(v0) = v0

x::bigint<v> & x != null
  -> x::node<p, q> * q::bigint<v1> & v = F(p, v1)
  
     res::node<p, r> * r::bigint<vr1> & vr = F(p, vr1) & vr1 = G(v1)
    
    POST:
     v0 = G(v0) ->
      v0 = g1*v0 + g2
      (1-g1)*v0 + g2 = 0
     
     vr = G(v) -> 
      F(p, vr1) = G(F(p, v1))
      F(p, G(v1)) = G(F(p, v1))
      f1*p + f2(g1*v1 + g2) + f3 = g1*(f1*p + f2*v1 + f3) + g2 
      (forall p) f1*(1-g1)*p + g2*(f2-1) + f3*(1-g1) = 0 (f2 != 0)
      -> f1 = 0 or g1 = 1
         f2 = 1 or g2 = 0
         f3 = 0 or g1 = 1
    
    RANK:
     v > v1 ->
      F(p, v1) > v1
      f1*p + f2*v1 + f3 > v1
      f1*p + (f2-1)*v1 + f3 > 0
      -> f2 = 1 and
         f1*p + f3 > 0 forall 0 <= p <= 9
         -> f1 = 0 and f3 = 1
*/     

