
data node{
 int val;
 node next;
}

ll<n> == self=null & n=0 or
  self::node<_,q>*q::ll<n-1>
  inv n>=0;

relation P(ann a).

int length(node x)
  infer [P]
  requires x::ll<n>@b & P(b)
  ensures  x::ll<n>@a;
{
  if (x == null) return 0;
  else{
    dprint;
    //x::ll<n>@b&x'=x & x!=null & P(b)&
    int tmp = length(x.next);
    dprint;
    return tmp + 1;
  }
}


/**

from where do i get RELASS [P]: ( P(b)) -->  not(b<:@L)] ?

!!! **cvutil.ml#1217:elim_abs (pure):[]
*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P]: ( P(b)) -->  b<:@A,
RELASS [P]: ( P(b)) -->  b<:@L,
RELDEFN P: ( P(b) & b<:@L & b<:b_1433) -->  P(b_1433),
RELASS [P]: ( P(b)) -->  not(b<:@L)]
*************************************

!!! **immutable.ml#62:imm + pure:[( not(b<:@L) & b<:@L & b<:@A, true)]
!!! **immutable.ml#64:imm + pure:[( false, true)]
***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [P]: ( P(b)) -->  true]
*****************************************

*/
