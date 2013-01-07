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

