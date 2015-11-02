WSS<p> ==
  self::WFSeg<q> * q::char_star<0, p> 
  inv self!=null;
  
WFS<n> ==
  self::char_star<0,q> & n = 0
  or self::char_star<v,q> * q::WFS<n-1> & v!=0
  inv n>=0;

WFSeg<p> ==
  self = p
  or self::char_star<v,q> * q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  //self = null or 
  self::char_star<v,q>*q::BADS<> 
  inv true;

//lemma_safe self::WFSeg<p,n1+n2> <- self::WFSeg<q,n1>*q::WFSeg<p,n2>.

//lemma_safe self::WFS<> <-> self::WFSeg<q,n>*q::char_star<0,q2>*q2::BADS<>.

HeapPred P(char_star x).

void loop (char_star s)
  infer [
    @shape_pre
    //P
    ,@pure_field,@classic
  ]
  //requires P(s)
  requires true
  ensures true;
{
  int x = get_char(s);
  if (x != 0) {
    s = plus_plus_char(s);
    loop(s);
  }
}
