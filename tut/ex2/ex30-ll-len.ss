data node {
  int val;
  node next;
}

/*
ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

HeapPred PP(node x).
PostPred QQ(node x).

int length(node x)
  infer [PP,QQ]
  requires PP(x)
  ensures QQ(x);
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex30-ll-len.ss

Can the (4,5) be printed in a standard way {FLOW,(4,5)=__norm#E}
or just omitted.

[ PP(x_1387) ::= 
 PP(next_21_1385) * x_1387::node<val_21_1384,next_21_1385>
 or emp&x_1387=null
 (4,5),
 QQ(x_1388) ::= PP(x_1388)(4,5)]
*************************************
*/
