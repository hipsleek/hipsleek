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

node insert(node x, node y)
  requires x::sortHO<a,R> * y::node<v,null>
  ensures  res::sortHO<b,R> & (v>a & b=a | (a>=b & b=v));

relation P(int a, int b) .

node sort(node x)
     infer [R0,P]
     requires x::ls<a>
     ensures  res::sortHO<b,R0> & P(b,a);
     //b<=a ;
/*

WHY did we have superfluous vars r_674,a_675?
Weren't they quantified in the fixcalc input?
If so, they should NOT be present in the final answer.

!!! REL POST :  P(b,a)
!!! POST:  a=b | (b<a & r_674<=a_675)

We derived:

[RELASS [P,R0]: ( R0(r_644,a_645)) -->  r_644<=a_645,
RELDEFN R0: ( r_674<=a_675) -->  R0(r_674,a_675),

RELDEFN P: ( a=b) -->  P(b,a),
RELDEFN P: ( R0(r_644,a_645) & P(b_642,a_631) & 
 ((a=b & b<=b_642 & r_644<=a_645) | 
 (b=b_642 & b_642<a & r_644<=a_645))) -->  P(b,a)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R0(r_674,a_675), r_674<=a_675, true, true),
( P(b,a), a=b | (b<a & r_674<=a_675), true, true)]

*************************************

!!! REL POST :  P(b,a)
!!! POST:  a=b | (b<a & r_674<=a_675)
!!! REL PRE :  true
!!! PRE :  true
!!! REL POST :  R0(r_674,a_675)
!!! POST:  r_674<=a_675
!!! REL PRE :  true
!!! PRE :  true


P:={[a] -> [b] -> []: (b=a ||  (exists (a_631: (exists (b_642: (exists (a_645: (exists (r_644:((((b=a && (a<=b_642 && r_644<=a_645)) 
|| (b_642=a && (a<b && r_644<=a_645))) 
&& R0(r_644,a_645)) 
&& P(b_642,a_631)))) )) )) )) )
};R0:={[] -> [r_674,a_675] -> []: r_674<=a_675
};
bottomupgen([P,R0], [2,2], SimHeur);

RELDEFN P: ( a=b) -->  P(b,a),
RELDEFN P: ( P(b_642,a_631) & 
 ((a=b & b<=b_642 & r_644<=a_645) | 
 (b=b_642 & b_642<a & r_644<=a_645))) -->  P(b,a)]

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

