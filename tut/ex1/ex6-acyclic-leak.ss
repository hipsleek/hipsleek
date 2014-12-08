data node {
  int val;
  node next;
}

ll<> == emp & self=null
  or self::node<_,q>*q::ll<>
  inv true;

int length(node x)
  infer[@classic]
  requires x::ll<>
  ensures emp;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex6-acyclic-leak.ss

@classic option?

 */
