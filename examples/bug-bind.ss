data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

// bug triggered by presence of global

global int a;

/*

File "bug-bind.ss", line 22, col 2: x2_local_2 is not defined
Fatal error: exception Failure("Error detected")

*/

/*

int foo2(node x)
	requires x::ll<n> & n>3
	ensures true;
{
  node x=x.next;
  int z;
  bind x to (v,n) in { z= v; } 
  return z;
}

*/

int foo2(node x)
	requires x::ll<n> & n>3
	ensures true;
{
  node x2=x.next;
  int z;
  bind x2 to (v,n) in { z= v; } 
  return z;
}


