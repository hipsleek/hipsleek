#include <string.h>

char* a (char* s)
  /*@
    requires true
    ensures res="ab"^"c";
  */
{
  s = "abcd";
  return s;
}

