/* selection sort */

data node {
	int val; 
	node next; 
}


sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R(int r, int a) == r<=a .

relation R2(int r, int a).

node insert(node x, node y)
     infer [R2]
     requires x::sortHO<a,R> * y::node<v,null> 
     ensures  res::sortHO<b,R2> & (v>a & b=a | (a>=b & b=v));
/*

[RELDEFN R2: ( b<=v2_670) -->  R2(b,v2_670),
RELDEFN R2: ( r_743<=a_744) -->  R2(r_743,a_744),
RELDEFN R2: ( v2_708<=v2_726) -->  R2(v2_708,v2_726),
RELDEFN R2: ( v2_708=v_616 & b<=v2_708 & v2_708<=v2_726 & R2(v_616,v2_726)) -->  R2(b,v2_708),
RELDEFN R2: ( b<v2_751) -->  R2(b,v2_751),
RELDEFN R2: ( b<=v2_791) -->  R2(b,v2_791)]

!!! REL POST :  R2(b,v2_670)
!!! POST:  b<=v2_670
!!! REL PRE :  true
!!! PRE :  true
Procedure insert$node~node SUCCESS


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

