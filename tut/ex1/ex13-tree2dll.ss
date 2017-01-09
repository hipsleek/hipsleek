data node2 {
  int val;
  node2 left;
  node2 right;
}

tree<> == emp & self=null 
  or self::node2<_,p,q>*p::tree<>*q::tree<> 
  inv true;

dll<pr> == emp & self=null 
  or self::node2<_,pr,q>*q::dll<self> 
  inv true;

node2 append(node2 x, node2 y)
  requires x::dll<a> * y::dll<b> 
  ensures res::dll<_>;

node2 flatten(node2 x)
     requires x::tree<> 
     ensures  res::dll<null> & res=x;
{
	node2 tmp;
        if (x==null) return x;
        tmp = append(flatten(x.left),flatten(x.right));
	x.left = null;
	x.right = tmp;
	if (tmp != null) tmp.left = x;
        return x;
}
