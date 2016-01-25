#include <stdlib.h>

/*@

WSS<p, n> ==
  self::WFSeg<q, n> * q::char_star<0, p> 
  inv self!=null;
  
WFSeg<p, n> ==
  self = p & n = 0
  or self::char_star<v, q> * q::WFSeg<p, n-1> & v!=0
  inv n >= 0;
*/

void loop (char* s)
/*@
  infer [
    @shape_pre
    //P
    ,@pure_field,@classic
    ,@size
  ]
  //requires P(s)
  requires true
  ensures true;
*/
{
  int x = *s;
  if (x != 0) {
    s++;
    loop(s);
  }
}

int main()
{
    int length = __VERIFIER_nondet_int();
    if (length < 1) { length = 1; }
    char* nondetString = (char*) alloca(length * sizeof(char));
    //@ dprint;
    nondetString[length-1] = '\0';
    //@ dprint;
    loop(nondetString);
    return 0;
}
