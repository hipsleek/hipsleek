
data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int),mi,mx> == 
  self::node<mi,null> & mi=mx 
  or self::node<v, p> * p::sortHO<v2,R,mi2,mx2> & R(v,v2) & mi=min(v,mi2) & mx=max(v,mx2) 
inv self!=null;

relation R0(int r, int a).
relation R1(int r, int a).
relation R2(int r, int a).

relation R(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .

node id(node x)
  infer [R1,R2]
  requires x::sortHO<a,R1,mi,mx>
  ensures  res::sortHO<a,R2,mi,mx> & res=x;
/*
  best pre/post spec is just:

  requires x::sortHO<a,R1,mi,mx>
  ensures  res::sortHO<a,R2,mi,mx> 
           & res=x & R1(a,b)->R2(a,b);

  which has a relational constraint in the
  post-condition


  # R1(a,b)-->R2(a,b)

  RELDEFN R2: ( a=a_30 & v2_590=v2_622 & R1(a,v2_590)) -->  R2(a_30,v2_622)]

Not useful to obtain:

*************************************
[( R2(a_30,v2_656), false, true, true)]
*************************************

!!! REL POST :  R2(a_30,v2_656)
!!! POST:  false
!!! REL PRE :  true
!!! PRE :  true
Procedure id$node SUCCESS

Above is not really a POST condition.
If we have: 
  R2(a,v) == false
We require:
  R1(a,v) --> false
But deriving false for pred relation
is a bad thing since it specializes the
predicate too much.

Thus, best to keep result as R1(a,b)->R2(a,b)

*/
{
    node tmp = x.next;
    if (tmp==null) return x;
    else {
      tmp=id(tmp);
      return x;
    }
}

