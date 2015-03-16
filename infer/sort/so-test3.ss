data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int)> == self=null
  or self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) & p!=null
inv true;

/*should not rename relation when unfold*/
void foo(node x)
  infer[X1]
  requires x::sortHO<m,X1>
  ensures  true;
{
  node t;
  if (x != null)
    t = x.next;
  dprint;
  return;
}
