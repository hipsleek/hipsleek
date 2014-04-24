/* insertion sort with infinity */
// run with --dsd --en-inf

data node{
	int val;
	node next;
}

sortll<mi> == self=null & mi=\inf 
	or self::node<mi, p> * p::sortll<m2> & mi<=m2 
	inv true;	
	
node insert(node x,node y)
requires x::sortll<a> * y::node<v,null>
ensures  res::sortll<b> & b=min(a,v);
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
