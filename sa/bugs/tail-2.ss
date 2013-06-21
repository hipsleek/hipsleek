data node{
	int val;
	node next;
}

HeapPred H1(node a,node y).
HeapPred G1(node a, node b, node y).

node foo (node c, node y)
  infer[H1,G1] 
  requires H1(c,y) 
  ensures G1(res,c,y);
{
    c.next =y;
    return c.next;
}

/*
# bugs/tail-2.ss

GOT
===
[ H1(c_799,y_800) ::= c_799::node<val_14_782,next_14_783>@M 
   * HP_784(next_14_783,y_800)& XPURE(HP_785(y_800)),
 G1(res_801,c_802,y_803) ::= c_802::node<val_14_782,res_801>@M&res_801=y_803]

HP_784 is a dangling predicate
HP_785 is an unknown pred from y paramter.
  why did it has only one parameter? The
  relational assumption had two parameters.

[ H1(c,y)&true --> c::node<val_14_782,next_14_783>@M * 
  HP_784(next_14_783,y@NI) * HP_785(y,c@NI)&true,

  
EXPECT
======
[ H1(c_799,y_800) ::= c_799::node<val_14_782,next_14_783>@M 
   * HP_785(y_800,?) &  XPURE(HP_784(next_14_783,y_800)),
  G1(res_801,c_802,y_803) ::= 
   c_802::node<val_14_782,res_801>@M * HP_785(y_800,?) &res_801=y_803
  HP_785(y_800,?) ::= NONE

*/

