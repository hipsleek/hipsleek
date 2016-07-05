/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi,mx> == self::node<v,null> & mi=v & mx=v 
  or self::node<v, p> * p::llMM<mi2,mx2> 
     & mi=min(v,mi2) & mx=max(v,mx2)
inv self!=null;


relation R(int a1, int a2,int a3).
relation P(int a1, int a2,int a3,int a4, int a5).

node insert(node x, node y)
     infer [P]
     requires x::llMM<mi,mx> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<mi2,mx2> & P(mi,mx,a,mi2,mx2);

{
    if (y.val<=x.val) {
        y.next = x; return y;
    } else {
      if (x.next==null) x.next=y;
      else {
        x.next = insert(x.next,y);
      };
      return x;
    }
}

