data node {
	int val;
	node next;
}

sortl<n,mi,mx> == self::node<mi,null> & mi=mx & n=1
	or self::node<mi, q> * q::sortl<n-1,k,mx> & mi<=k
	inv n>=1 & mi<=mx;

node insert(node x, node vn)
	requires x::sortl<n,sm,lg> * vn::node<v,_>
    	ensures res::sortl<m,ns,nl> & ns=min(v,sm) & nl=max(v,lg) & m>=n;
{ 	
       if (vn.val<x.val) {
		vn.next = x;
		return vn;
        } 
	else if (x.next==null) {
		x.next = vn; vn.next = null; 
		return x; } 
	else {  x.next = insert(x.next, vn); 
		return x; }
}


