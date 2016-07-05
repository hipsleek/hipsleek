/*
in prelude.ss
data char_star {
  int val;
  char_star next;
}
*/

pred WSS<p> ==
  self::WFSeg<q>*q::char_star<0,p> 
  inv self!=null.

pred WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

pred WFG<p> ==
  self::char_star<0,p>
  or self::char_star<v,q>*q::WFG<p> & v!=0
  inv self!=null.

lemma_safe self::WFG<p> -> self::WFSeg<q>*q::char_star<0,p>.


  /*
==> unknown segment
  P(x,d) -> U(x,q) * q::chr<0,d>

==> segmented-pred
  P(x,d) -> U(x,q) * q::chr<v,d>
  U(x,q) -> x=q
  U(x,q) -> x::chr<v,q1>*U(q1,q) & v!=0




*/
