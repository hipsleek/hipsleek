WSSN<p, n> ==
  self::WFSegN<q, n-1> * q::char_star<0, p> * p::MEM<>
  inv self!=null & n>=0;
  
WFSegN<p, n> ==
  self = p & n = 0
  or self::char_star<v, q> * q::WFSegN<p, n-1> & v!=0
  inv n>=0;

WSS<p> ==
  self::WFSeg<q> * q::char_star<0, p> // * p::MEM<> 
  inv self!=null;
  
WFSeg<p> ==
  self = p
  or self::char_star<v, q> * q::WFSeg<p> & v!=0
  inv true;
  
MEM<> ==
  self = null or
  self::char_star<_, p> * p::MEM<>;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

char_star alloc_str (int n)
  requires Term
  case {
    n < 0 -> ensures res = null;
    n >= 0 -> ensures res::WFSegN<p, n> * p::MEM<>; 
  }
  
void finalize_str (char_star s, int n)
  requires s::WFSegN<p, m> * p::MEM<> & 0 <= n & n < m & Term
  //ensures s::WFSegN<q, n> * q::char_star<0, r> * r::MEM<>;
  ensures s::WSSN<q, n+1> * q::MEM<>;

HeapPred P(char_star s).
HeapPred Q(char_star s, char_star t).

void loop (ref char_star s)

  infer [
    //@shape_post,
    //P
    Q
    ,@pure_field,@classic
    //,@size
  ]
  //requires P(s)
  //requires true
  //ensures true;
  
  requires s::WSS<p>
  ensures Q(s, s');

  //requires s::WFSegN<q, n> * q::char_star<0, p>
  //requires s::WSSN<p, n> * p::MEM<>
  //ensures s::WFSegN<s', n-1> * s'::char_star<0, p> * p::MEM<>;
{
  int x = get_char(s);
  if (x != 0) {
    s = plus_plus_char(s);
    loop(s);
  }
}

/*
void main () 
  requires true
  ensures true;
{
  int length = 0;
  //if (length < 1) length = 1;
  char_star str = alloc_str(length);
  dprint;
  finalize_str(str, length-1);
  dprint;
  loop(str);
  dprint;
}
*/
