data node {
  int val;
  node next;
}


relation R(node x).
relation P(node x).


node append (node x,node y)
  infer [@ana_ni,R,P]
  requires R(x) & P(y)
  ensures true;
{
   if (x==null) return y;
   else{
     x = append(x.next, y);
     return x;
   }
 }


/*
*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(x)) -->  x!=1,
RELDEFN R: ( 2<=v_node_18_1692') -->  R(v_node_18_1692')]
*************************************

!!! **immutable.ml#62:imm + pure:[( true, x!=1)]
!!! **immutable.ml#64:imm + pure:[( true, x!=1)]
***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [R]: ( R(x)) -->  x!=1]
*****************************************

 */

