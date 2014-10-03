/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity

ls<v> == 
  self::node<v,null> 
  or self::node<v, p> * p::ls<v2>  
inv self!=null;

sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R0(int r, int a).
relation R1(int r, int a).

relation R(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .

node insert(node x, node y)
  requires x::sortHO<a,R> * y::node<v,null>
  ensures  res::sortHO<b,R> & (v>a & b=a | (a>=b & b=v));

relation P(int a, int b) .

node sort(node x)
     infer [R0,R1]
     requires x::sortHO<a,R0>
     ensures  res::sortHO<b,R1> & b<=a;
     //b<=a ;
/*

[RELASS [R0,R1]: ( R1(r_647,a_648)) -->  r_647<=a_648,
RELDEFN R1: ( r_677<=a_678) -->  R1(r_677,a_678)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R1(r_677,a_678), r_677<=a_678, true, true)]
*************************************

!!! REL POST :  R1(r_677,a_678)
!!! POST:  r_677<=a_678
!!! REL PRE :  true
!!! PRE :  true
Procedure sort$node SUCCESS

*/
{
    node tmp = x.next;
    if (tmp==null) return x;
    else {
      x.next=null;
      tmp=sort(tmp);
      return insert(tmp,x);
    }
}

