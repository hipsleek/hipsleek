data node {
  int val;
  node left;
  node right;
}

tree<> == emp & self=null 
  or self::node<_,p,q>*p::tree<>*q::tree<> 
  inv true;

dll<pr> == emp & self=null 
  or self::node<_,pr,q>*p::dll<self> 
  inv true;

node append(node x, node y)
  requires x::dll<a> * y::dll<b> 
  ensures res::dll<_>;

node flatten(node x)
	requires x::tree<> 
        ensures  res::dll<_> & res=x;
{
	node tmp;
        if (x==null) return x;
        tmp = append(flatten(x.left),flatten(x.right));
	//x.left = null;
        dprint;
	x.right = tmp;
	if (tmp != null) tmp.left = x;
        return x;
}


/*


*/
