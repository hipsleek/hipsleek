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

node sort(node x)
     infer [R0]
     requires x::ls<a>
     ensures  res::sortHO<b,R0> & b<=a ;
/*

We derived:

Checking procedure sort$node... 
*************************************
*******pure relation assumption ******
*************************************
[RELASS [R0]: ( R0(r_643,a_644)) -->  r_643<=a_644,
RELDEFN R0: ( r_643<=a_644 & r_673<=a_674 & R0(r_643,a_644)) 
                -->  R0(r_673,a_674)]

However  R0(r_643,a_644) is not really connected to
the output on RHS. Actually, we should have obtained
below instead if we only traverse the connected
formula on the LHS.

// --dis-pre-residue gives
*************************************
*******pure relation assumption ******
*************************************
[RELASS [R0]: ( R0(r_643,a_644)) -->  r_643<=a_644,
RELDEFN R0: ( r_673<=a_674) -->  R0(r_673,a_674)]
*************************************


Why false inferred?

*************************************
[RELASS [R0]: ( R0(r_643,a_644)) -->  r_643<=a_644,
RELDEFN R0: ( r_643<=a_644 & r_673<=a_674 & R0(r_643,a_644)) 
                -->  R0(r_673,a_674)]
*************************************

!!! REL POST :  R0(r_673,a_674)
!!! POST:  false
!!! REL PRE :  true
!!! PRE :  true
Procedure sort$node SUCCESS

fixcalc currently formed:

R0:={[] -> [r_673,a_674] -> []: 
#r_673<=a_674 || 
(exists (a_644: (exists (r_643:((r_643<=a_644 && r_673<=a_674) && R0(r_643,a_644)))) )) 
};

without base-case. Not sure if R0 should be classify as a post-relation.
It is actually a relation in a predicate, rather than a relation
that forms to post-condition.

Doing least-fix-point without a base-case seems unsound
for such pred-relation.

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

