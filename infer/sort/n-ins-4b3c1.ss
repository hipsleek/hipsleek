/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<v> == self::node<v,null>  
  or self::node<v, p> * p::llMM<_> 
inv self!=null;

relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).

node insert(node x, node y)
     infer [P5]
     requires x::llMM<v> * y::node<a,null> 
      //& R(a,mi,mx)
     ensures  res::llMM<v2> 
         & P5(v2,v,a)
     ;
/*

P5 indicates that sorting is based on an ascending technique

!!! REL POST :  P5(v2,v,a)
!!! POST:  (a=v2 & a<=v) | (v=v2 & v2<a)
!!! REL PRE :  true
!!! PRE :  true

*/
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

