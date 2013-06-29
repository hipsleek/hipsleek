data node {
  int val;
  node next;
}


HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a,node b).
HeapPred HP1(node a, node b).
//HeapPred G1(node a, node b, node c).


ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void append(node x, node y)
  infer[H2,G2]
  requires H2(x,y)
  ensures G2(x,y);
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/*

H2(x_886,y_887) ::= x_886::node<val_34_821,next_34_822>@M 
 * HP_823(next_34_822,y_887) * HP_824(y_887,x_886)&true,

G2(x_888,y_889) ::= x_888::node<val_34_821,y_890>@M 
     * HP_891(y_890,y_889)&true,

HP_823(next_34_822,y) ::= 
 next_34_822::node<val_34_821,next_34_822>@M 
   * HP_823(next_34_822,y) * HP_824(y,next_34_822)&true
 or H2(next_34_822,y)&next_34_822!=null
 ,

HP_891(y_890,y_889) ::= 
 HP_824(y_889,x_888)&y_889=y_890
 or y_890::node<val_34_821,y_892>@M * HP_891(y_892,y_889)&true
 ,

 HP_824(y,x) ::=NONE]

 */
