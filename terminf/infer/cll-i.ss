data node {
  int val;
  node next;
}

lseg<L, p> == 
  self = p & L = l0 or 
  self::node<v, q> * q::lseg<L1, p> & L = f(L1);

clist<C> ==
  self::node<v, q> * q::lseg<L, self> & C = g(L);
  
lemma self::lseg<L1, q> & L1 = f_l(L) <- self::lseg<L, p> * p::node<v, q>;

lemma self::clist<C> & C = g_l(L) <- self::lseg<L, q> * q::node<v, self>;

int length (node x)
  requires x::clist<C>
  ensures res > 0;
{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}