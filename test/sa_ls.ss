data node {
	int val; 
	node next;	
}

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

ls<p> == self=p 
	or self::node<_, q> * q::ls<p>
	inv true;

ll<> == self=null 
	or self::node<_, q> * q::ll<>
	inv true;

void ex41 (node y, ref node x)
// Ex 4.1
  requires x::lseg<y,n> & n>0
  ensures  x::lseg<y,n> & x'=y; //'
  requires x::node<_,q>*q::ls<y> 
  ensures  x::node<_,q>*q::ls<y> & x'=y; //'
{
  x = x.next;
  if (x!=y) ex41(y,x);
}

void ex42 (ref node x)
// Ex 4.1
  requires x::lseg<null,n> & n>0
  ensures  x::lseg<null,n> & x'=y; //'
  requires x::node<_,q>*q::ls<null> 
  ensures  x::node<_,q>*q::ls<null> & x'=null; //'
  requires x::node<_,q>*q::ll<> 
  ensures  x::node<_,q>*q::ll<> & x'=null; //'
  requires x::ll<> & x!=null 
  ensures  x::ll<> & x'=null; //'
{
  x = x.next;
  if (x!=null) ex42(x);
}

