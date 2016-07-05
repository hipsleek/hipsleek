/* selection sort */

data node {
	int val; 
	node next; 
}


sortA<v> == self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 
inv self!=null;

llMM<v,mi,mx> == self::node<v,null> & mi=v & mx=v 
  or self::node<v, p> * p::llMM<_,mi2,mx2> 
     & mi=min(v,mi2) & mx=max(v,mx2)
inv self!=null;


relation R(int a1, int a2,int a3, int a4).
relation P(int a1, int a2,int a3,int a4, int a5,int a6, int a7).

node insert(node x, node y)
     infer [R,P]
     requires x::llMM<v,mi,mx> * y::node<a,null> & R(a,v,mi,mx)
     ensures  res::llMM<v2,mi2,mx2> & P(v,mi,mx,a,v2,mi2,mx2);

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

