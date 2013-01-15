data node {
	int val; 
	node next;	
}

int test1 (node x, node y)
  infer [v]
  requires x::node<v1,_>@v * y::node<v2,_>@v
  ensures res = v1 + v2;
{
  return sum2(x,y);
}

int test2 (node x, node y)
  infer [v]
  requires x::node<v1,_>@v  
  ensures res = v1 + v1;
{
  return sum2(x,x);
}


/* usage of & */
/* int sum1(node x, node y) */
/*   infer [v] */
/*   requires x::node<a,_>@v * y::node<b, _>@v    */
/*   ensures res = a + b; */
/* { return x.val + y.val; dprint;} */


int sum2(node x, node y)
  /* infer [v] */
  /* requires (x::node<a, _>@v & y::node<b, _>@v) // fails*/
  /* requires (x::node<a, _>@I & y::node<b, _>@I) // fails*/
  requires (x::node<a, _>@L & y::node<b, _>@L)
  ensures res = a + b;
{ return x.val + y.val; dprint;}

