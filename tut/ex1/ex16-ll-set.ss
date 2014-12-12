data node {
  int val;
  node next;
}

ll<S> == emp & self=null & S={}
  or self::node<v,q>*q::ll<S1> & S=union({v},S1)
  inv true;

int length(node x)
  requires x::ll<S>
  ensures x::ll<S> & res>=0;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}


