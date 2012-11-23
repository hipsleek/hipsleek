data node {
  int val;
  node next;
}


ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int hd0(ref node x)
 infer [x] 
 requires true
 ensures true; //'
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  x = x.next;
  return x.val;
}

int hd1(node x)
 infer [x] 
 requires true
 ensures true; //'
/*
   requires x::node<inf1,inf2>
   ensures res=inf1;
*/
{
  return x.val;
}


int hd2(node x)
 infer [x] 
 requires x::ll<n>
 ensures true; //'
/*
   requires x::ll<n> & x!=null
   ensures x::ll<n> 
*/
{
  return x.val;
}

int hd3(node x)
 infer [n] 
 requires x::ll<n>
 ensures true; //'
/*
   requires x::ll<n> & n>0
   ensures  x::ll<n> 
*/
{
  return x.val;
}

// infer_vars = [] -> still got new post?
int hd4(node x)
 infer [] 
 requires x::ll<n>
 ensures true; //'
/*
   requires x::ll<n> & n>0
   ensures  x::ll<n> 
*/
{
  return x.val;
}
