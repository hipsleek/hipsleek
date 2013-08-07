data node {
  int val;
  node next;
}

HeapPred G2(node a, node b).
HeapPred H1(node a).



H1_delete<> == self = null
or
 next_24_523PRM::H1_delete<> * self::node<val_24_590, next_24_523PRM> inv true;

G2_delete<x_596> == self = null & (x_596=self | x_596!=self)
or
 self::node<val_24_522PRM, next_24_591> * next_24_591::G2_delete<x_593> inv true;

HP_553_delete<> == self::H1_delete<> inv true;




node delete(node x, int a)
/*requires x::ll1<> & a > 0 
   ensures x::ll1<>; */

//G1 can not be a lseg because y!=null
/*  infer[H1,G2]
  requires H1(x)
     ensures G2(res,x) ;
*/
	requires x::H1_delete<> ensures res::G2_delete<x>;


{
  	if (x == null)
		return x;
	else
  {
		if (x.val == a)
		{
			node t = x.next;
                        //	dprint;
			return t;
		}
		else
	  { node tt = new node(x.val, delete(x.next, a)) ;
		//dprint;
            //	assume false;
		return tt;
	  }
  }
}
