#include <stdlib.h>

/*@
WSS<p> ==
  self::WFSeg<q> * q::char_star<0, p> 
  inv self!=null;
  
WFSeg<p> ==
  self = p
  or self::char_star<v,q> * q::WFSeg<p> & v!=0
  inv true;
*/

void loop (char* s)
/*@
  infer [
    @shape_pre
    //P
    ,@pure_field,@classic
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
