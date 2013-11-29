data node {
  int val;
  node next;
}

lseg<p> == 
  self = p or self::node<v, q> * q::lseg<p>;

clist<> ==
  self::node<v, q> * q::lseg<self>;
  
lemma self::lseg<q> <- self::lseg<p> * p::node<v, q>;

lemma self::clist<> <- self::lseg<q> * q::node<v, self>;

int length_l (node x)
  requires x::node<_, p> * p::lseg<x>
  ensures res > 0;
{
  if (x == null)
    return 0;
  else
    return 1 + length_l(x.next);
}

int length (node x)
  requires x::lseg<null>
  ensures res >= 0;
  
  requires x::node<_, p> * p::lseg<x>
  ensures res >= 0;
{
  if (x == null) return 0;
  else return length_aux(x, x);
}

int length_aux (node hd, node x)
  requires x::lseg<null> & x != null
  ensures res > 0;
  
  requires hd::lseg<x> * x::node<_, p> * p::lseg<hd>
  ensures res > 0;
{
  if (x.next == null || x.next == hd)
    return 1;
  else return 1 + length_aux(hd, x.next);
}

