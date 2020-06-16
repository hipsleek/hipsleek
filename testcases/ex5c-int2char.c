#include <stdio.h>

char* __cast_int_star_to_char_star__(int p[])
/*@
  case{
  p != null -> requires p::int_star<_>
               ensures  res::char_star<_,_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

char *a;

int main(void)
/*@
  requires a::char_star<_>
  ensures  a::char_star<101,b> * b::char_star<112,c> * c::char_star<121,d> * d::char_star<116,null> * ;
*/
{
  /*@ dprint; */
  /*
   * little-endian integer interpretation of "epyt" 101 112 121 116, is 1954115685
   */
  int s = 1954115685;
  a = (char *)&s;
  //printf("%c%c%c%c\n", *a, *(a+1), *(a+2), *(a+3));
}
