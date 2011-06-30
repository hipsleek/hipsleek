/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

	
	

/* return the tail of a singly linked list */
node get_next(node x)
	/* requires x::ll<n> & n > 0 */
	/* ensures x::ll<1> * res::ll<n-1>;  */
  requires x::node<v,q>
  ensures x::node<v,null> & res=q;
  requires x=null 
  ensures x=null & flow __Error;
 case {
   x=null -> ensures true & flow __Error;
   x!=null -> 
     requires x::node<v,q>
     ensures x::node<v,null> & res=q;
 }
 requires x::ll<n> & x!=null
 ensures x::ll<1> * res::ll<n-1>;
{
  //dprint;
	node tmp = x.next;
	x.next = null;
	return tmp;
}


void foo(node x)
  requires x::ll<n>
  ensures true;
{
  if (x!=null) {
    node y = get_next(x);
  }
}

void foo1(node x)
  requires x::ll<n>
  ensures true;
{
  if (x!=null) {
    node y = get_next(x);
  }
}

lseg<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg<p, n-1> & self!=p
	inv n>=0;

ll_tail<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail<tx, n-1> & r!=null
	inv self!=null & tx!=null & n>=1;

/* coercion "lseg2" self::lseg<p, n> <- self::lseg<q, n1> * q::lseg<p, n2> & n=n1+n2; */
/* coercion "ll_tail2" self::ll_tail<t, n> <-> self::lseg<t, n-1> * t::node<_, null>; */

int upto(node x, node p)
  /* requires x::lseg<p,n> */
  /* case { */
  /*   x=p  ->  ensures res=0; */
  /*   x!=p  -> ensures res=n; */
  /* } */
  /*    case  */
  /*     { p=null -> ensures true & flow __Error; */
  /*       p!=null -> ensures res=n; */
  /*     } */
  /* } */
  
  requires x::lseg<p,n> & x=p //& x!=null
  ensures res=0;
   /* requires x::lseg<p,n> & n>0 */
  /* ensures res = n; */
{
  if (x==p) return 0;
  else return 1+upto(x.next,p);
}

 int sqrt(int v)
 case {
   v>=0 -> ensures res>=0;
   v<0 -> ensures true & flow __Error;
 }
 /* requires v>=0 */
 /* ensures res>=0; */
 /* requires v<0 */
 /* ensures true & flow __Error; */

 pos<> == self=null 
      or self::node<v,q> * q::pos<> & v>=0
      inv true;

 one_neg<> == self::node<v,q>  & v<0
    or self::node<v,q> * q::one_neg<> //& v>=0
  inv self!=null;

 int sumsqrt(node x)
   requires x::pos<>
   ensures  res>=0;
   requires x::one_neg<>
   ensures  true & flow __Error;
{
  if (x==null) return 0;
  else return sqrt(x.val)+sumsqrt(x.next);
}



