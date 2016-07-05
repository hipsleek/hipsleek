/* 2-3 trees */
data node3 {
	int maxl;	// max left
	int maxm;	// max middle	
	node3 left;
	node3 middle;
	node3 right;
}


tree2_3<h,n> == self = null & h = 0 & n = 0
	or self::node3<_, _, l, m, r> * l::tree2_3<hl, nl> * m::tree2_3<hm, nm> * r::tree2_3<hr, nr> 
	& hl = hm & hl = hr & h = hl + 1
	& n=nl+nm+nr+2
	or self::node3<_, l, m> * l::tree2_3<hl, nl> * m::tree2_3<hm, nm> 
	& hl = hm & h = hl + 1
	& n=nl+nm+1
	inv h >= 0 & n>=0;





