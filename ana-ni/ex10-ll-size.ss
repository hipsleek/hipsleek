data node {
  int val;
  node next;
}

ll<> == self=null
  or self::node<_,q>*q::ll<>
inv true;

relation P(int a,int b).
relation Q(int a,int b, int c).

int size(node x)
  infer [@ana_ni,@shape_pre,@classic]//,R]
  requires true
 ensures true;
{
  if (x==null) return 0;
  else {
    return 1 + size(x.next);
  }
}
