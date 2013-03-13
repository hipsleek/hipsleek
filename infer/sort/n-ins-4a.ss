/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi> == self::node<v,null> & mi=v  
  or self::node<v, p> * p::llMM<mi2> 
  & mi=min(v,mi2)
inv self!=null;

relation R(int a1, int a2).
relation P(int a1, int a2,int a3).

node insert(node x, node y)
     infer [R,P]
     requires x::llMM<mi> * y::node<a,null> & R(a,mi)
     ensures  res::llMM<mi2> & P(a,mi,mi2);
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

