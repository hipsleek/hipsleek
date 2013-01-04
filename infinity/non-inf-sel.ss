/* insertion sort without infinity */

data node{
	int val;
	node next;
}

sortA<v> == self = null
	or self::node<v,null>
	or self::node<v,p> * p::sortA<v2> & v <= v2 & p != null
	inv true;
	
//sortll<mi> == self=null & mi=\inf 
//	or self::node<mi, p> * p::sortll<m2> & mi<=m2 
//	inv true;	
	
node insert(node x,node y)

//requires x::sortll<a> * y::node<v,null>
//ensures  res::sortll<b> & b=min(a,v);

requires y::node<v,null>
case{
	x = null -> ensures res::sortA<v> & res != null;
	x != null -> requires x::sortA<a>
			ensures res::sortA<b> & b = min(a,v) & res != null;
	}
{
if (x == null) return y;
else {
	if (y.val <= x.val){
		y.next = x;
		return y;
		}
	else {
	node tmp;
	tmp = insert(x.next,y);
	x.next = tmp;
	return x;
	}
}
}	
