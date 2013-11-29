data node {
  int val;
  node next;
}

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p>
  inv n>=0;

clist<n> ==
  self::node<v, q> * q::lseg<n-1, self>
  inv n>0;


lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;
  
lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;

//lemma self::node<v, q> * q::lseg<self> -> q::node<v1, s> * s::lseg<q>;

/*
int length_l (node x)
  requires x::node<_, p> * p::lseg<n, x> & Loop or
           x::lseg<n, null> & Term[n]
  ensures res >= 0;
{
  if (x == null)
    return 0;
  else
    return 1 + length_l(x.next);
}

int length (node x)
  requires x::lseg<n, null> & Term 
  ensures res = n;

{
  if (x == null) return 0;
  else return length_aux(x, x);
}
*/

int length_aux (node hd, node x)
  requires x::lseg<n2, null> & x != null & Term[n2]
  ensures res <= n2;
  
  //requires hd::lseg<_, x> * x::node<_, p> * p::lseg<n, hd> & Term[n]
  //ensures res = n + 1;
{
  if (x.next == null || x.next == hd)
    return 1;
  else return 1 + length_aux(hd, x.next);
}

