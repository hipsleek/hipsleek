/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity
/*
sortA<v> == self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 
inv self!=null;
*/

sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R(int r, int a).

node insert(node x, node y)
     infer [R]
     requires x::sortHO<a,R> * y::node<v,null>
     ensures  res::sortHO<b,R> & (v>a & b=a | (a>=b & b=v));
/*

Checking procedure insert$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R: ( true) -->  R(b,v2_668),
RELDEFN R: ( v2_616=v2_727 & R(a,v2_616)) -->  R(v2_709,v2_727),
RELDEFN R: ( v2_709=v_614 & a=v2_709 & v2_616=v2_727 & R(a,v2_616) & R(v_614,v2_727)) -->  R(b,v2_709),
RELDEFN R: ( true) -->  R(b,v2_760),
RELDEFN R: ( ((a<v2_803 & v2_803<=v2_616) | v2_616=v2_803) & R(a,v2_616)) -->  R(b,v2_803),
RELASS [R]: ( R(a,v2_616)) -->  a>=v2_616]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

Can we avoid the disjunction in the xform?

 unstructured formula: 
   {215}->EXISTS(v_19,flted_16_18: self::node<v_19,flted_16_18>@M[Orig]&
   flted_16_18=null & v=v_19&{FLOW,(1,25)=__flow})[]
   || {214}->EXISTS(v_20,p,v2: self::node<v_20,p>@M[Orig] * 
      p::sortHO<v2,R>@M[0][Orig][LHSCase]&R(v,v2) & v=v_20&
      {FLOW,(1,25)=__flow})[]
  xform: self!=null | self!=null

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

