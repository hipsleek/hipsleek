data node {
  int val;
  node next;
}



HeapPred H2(node a,node b).
HeapPred G2(node a, node b).
//HeapPred G1(node a, node b, node c).


void two(node x, node y)
/*
  requires x::node<_,n> * y::node<_,m>
  ensures x::node<_,n> * y::node<_,m>;
*/

  infer[H2,G2]
  requires H2(x,y)
  ensures G2(x,y);

{
  if (x.next == null)
    return;
  else {
    node tmp = y.next;
    return;
  }
}

/*

[ H2(x,y)&true --> x::node<val_24_783,next_24_784>@M * 
     HP_785(next_24_784,y@NI) * HP_786(y,x@NI)&true,
 
 HP_786(y,x@NI)--> y::node<val_27_794,next_27_795>@M * HP_796(next_27_795,x@NI)&true,

 HP_785(next_24_784,y@NI) * HP_786(y,x@NI) * 
  x::node<val_24_783,next_24_784>@M&next_24_784=null --> G2(x,y)&true,

 HP_785(next_24_784,y@NI) * x::node<val_24_783,next_24_784>@M * 
  HP_796(next_27_795,x@NI) * y::node<val_27_794,next_27_795>@M&
  next_24_784!=null --> G2(x,y)&true]


 */
