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
relation R1(int r, int a) == false.

relation R(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .
relation D(int r, int a) == r>=a .

node insert(node x, node y)
  requires x::sortHO<a,D> * y::node<v,null>
  ensures  res::sortHO<b,D> & (v>a & b=v | (a>=v & b=a));

node sort(node x)
     infer [R0]
     requires x::ls<a>
     ensures  res::sortHO<b,R0> 
           & b>=a  
          ;
/*

We derived:

*************************************
*******pure relation assumption ******
*************************************
[RELASS [R0]: ( R0(r_643,a_644)) -->  r_643<=a_644,
RELDEFN R0: ( r_673<=a_674) -->  R0(r_673,a_674)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R0(r_673,a_674), r_673<=a_674, true, true)]
*************************************

!!! REL POST :  R0(r_673,a_674)
!!! POST:  r_673<=a_674
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

