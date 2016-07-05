data node {
	int val; 
	node next;	
}
// I am not sure about the convention related to @I 
//  -> i undestood @I as any permission hence i translated it to a variable permission v,
//  -> if it is required that it is only read then it can be translated to  (v != full).


int test1 (node x, node y) 
  requires x::node<v1,_>@v * y::node<v1,_>@v
  ensures res = v1+v2;
{
  return sum1(x,y);
}

int test2 (node x, node y) 
  requires x::node<v1,_>@v      // this will also succeed as i can always split the v permission into two sub permissions during the entailment process
  ensures res = v1+v1;
{
  return sum2(x,x);
}


/* usage of & */
int sum1(node x, node y)
requires (x::node<a, _>@v * y::node<b, _>@v)   // changed the & back into *
ensures res=a+b;
{ return x.val + y.val; dprint;}


int sum2(node x, node y)
requires (x::node<a, _>@v * y::node<b, _>@v) 
ensures res=a+b;
{ return x.val + y.val; dprint;}

