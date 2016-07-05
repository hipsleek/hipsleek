data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* return the tail of a singly linked list */
node get_next(node x)
/*
  requires x::node<v,q>
  ensures x::node<v,null> & res=q;
*/
  requires x=null 
  ensures x=null & flow __Error;
{
  //dprint;
	node tmp = x.next;
        dprint;
	//x.next = null;
	return tmp;
}

int foo(node x)
  requires x::node<v,q> 
  ensures x::node<v,q>;
{
  int a;
  //dprint;
  a = x.next.val;
  //dprint;
  return a;
}
/*
int goo(node x, node y)
  requires x::node<v,q> & y = null
  ensures x::node<v,q>;
{
  int a;
  x = y;
  a = x.next.val;

  return a;
}
*/
