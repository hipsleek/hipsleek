
data node {
	int val; 
	node next;	
}

int ierror()
  requires true
  ensures true & flow __Error;

int add1(node x, node y)
  requires x::node<v1,null> * y::node<v2,null>
  ensures x::node<v1,null> * y::node<v2,null> & res=v1+v2;
/*
case {
x =null | y = null ->
x!= null & y =null ->
  case
  { x::node<v1,null> & x=y ->
    x::node<v1,null> * y::node<v2,null> ->
  }
}
 */
{
  if (x==null || y==null)
    return ierror();
  else
    return x.val + y.val;
}
