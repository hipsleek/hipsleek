data node {
  int val;
  node next;
}

ll<> == emp & self=null
  or self::node<_,q>*q::ll<>
  inv true;

/* non-touching list segment */
ls_nt<p> == emp & self=p
  or self::node<_,q>*q::ls_nt<p> & self!=p
  inv true;

/* possibly touching list segment */
ls<p> == emp & self=p
  or self::node<_,q>*q::ls<p> & self!=p
  inv true;

int length(node x)
  requires x::ll<>
  ensures x::ll<>;
  requires x::ls_nt<null>
  ensures x::ls_nt<null>;
  requires x::ls<p>
  ensures x::ls<p>;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
( [(,1 ); (,2 )]) bind: node  x'::node<val_29_1420',next_29_1421'>@L cannot be derived from context
ex8-lseg-fail.ss_29:23_29:29
*/

