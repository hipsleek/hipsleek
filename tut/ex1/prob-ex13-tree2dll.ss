data node {
  int val;
  node left;
  node right;
}

tree<> == emp & self=null 
  or self::node<_,p,q>*p::tree<>*q::tree<> 
  inv true;

dll<pr> == emp & self=null 
  or self::node<_,pr,q>*q::dll<self> 
  inv true;

node append(node x, node y)
  requires x::dll<a> * y::dll<b> 
  ensures res::dll<_>;

void skip() 
  requires true
  ensures true;

node add_front(node x,node tmp)
  requires x::node<_,_,_> * tmp::dll<_>
  ensures  res::dll<_> & res=x;
{
	x.right = tmp;
	if (tmp != null) tmp.left = x;
        return x;
}


node flatten(node x)
	requires x::tree<> 
        ensures  res::dll<_> & res=x;
{
	node tmp;
        if (x==null) return x;
        tmp = append(flatten(x.left),flatten(x.right));
	//x.left = null;
	x.right = tmp;
	if (tmp != null) tmp.left = x;
        return x;
}



/*
Exercise:

Write an implementation of flatten that would 
traverse each node only once; and verify that the
number of nodes is preserved in the dll.



*/
