/* selection sort */

data node {
	int val; 
	node next; 
}

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;

relation R(int a,int b,int c).

relation P(int a,int b).

node zip(node x, node y)
  infer [ll -> llN]
  requires x::ll<> * y::ll<> 
  ensures  res::ll<>;

{
  if (x==null) return null;
    else{
           x.val=x.val+y.val;
           x.next=zip(x.next, y.next);
           return x;
    }
}










