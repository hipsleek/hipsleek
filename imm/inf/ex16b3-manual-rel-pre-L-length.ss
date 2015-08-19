
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
simplify below:
@A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=max(b,b_1475) & 
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) & flted_8_1468=n_1476 & 
 b<:b_1475 & b<:@L & x'=x & P(b) & x'!=null & !(v_bool_18_1446') & 
 flted_8_1468+1=n & v_int_24_1445'=1+tmp_1497 & res=v_int_24_1445' & 
 (((1<=flted_8_1468 & q_1470!=null) | (q_1470=null & flted_8_1468=0))) & x'=2


@A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L


@A=imm_1486 & a_1495<:imm_1486 & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L
or
@A=a_1495 & imm_1486<:a_1495 & b=min(imm_1486,b_1475) & imm_1485=b_1475 &  //because b<:b_1475
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) 
 b<:b_1475 & b<:@L

=======================================================
from where do i get RELASS [P]: ( P(b)) -->  not(b<:@L)] ? (FIXED) - forgot to add the merge guards for view nodes

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


 @A=max(imm_1486,a_1495) & b=min(imm_1486,b_1475) & imm_1485=max(b,b_1475) & 
 @L<:imm_1485 & imm_1487=min(imm_1486,a_1495) & flted_8_1468=n_1476 & 
 b<:b_1475 & b<:@L & x'=x & P(b) & x'!=null & !(v_bool_18_1446') & 
 flted_8_1468+1=n & v_int_24_1445'=1+tmp_1497 & res=v_int_24_1445' & 
 (((1<=flted_8_1468 & q_1470!=null) | (q_1470=null & flted_8_1468=0))) & x'=2



*/
