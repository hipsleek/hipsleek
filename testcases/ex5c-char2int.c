#include <stdio.h>

int* __cast_char_star_to_int_star__(char p[])
/*@
  case{
  p != null -> requires p::char_star<_,_>
               ensures  res::int_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

int *a;

int main(void)
/*@
  requires a::int_star<_>
  ensures  a::int_star<1954115685>;
*/
{
  /*@ dprint; */
  /*
   * big-endian integer interpretation of "type" 116 121 112 101, is 1954115685
   */
  char s[] = {'e','p','y','t'}; // integer is little-endian
  a = (int *)s;
  //printf("%d\n", *a);
}
