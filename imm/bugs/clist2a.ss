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

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;

lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;

lemma self::node<v, q> * q::lseg<n, self> -> q::node<v1, s> * s::lseg<n, q>;

int length (node x)


//  infer [@term]
//  requires x::clist<n> ensures false;


  requires x::lseg<n,null>@L ensures res=n;
// good with and without --imm

  requires x::lseg<n,null>
  ensures x::lseg<n,null> & res=n;

{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}
/*
# clist1.ss

  requires x::clist<n> ensures false;

Why did we go into a loop with the above spec?
Is it due to lemma?

*/
