#include <string.h>

char* a (char *s)
  /*@
    requires true
    ensures s="abc" & res="abc";
  */
{
  s = "abc";
  return s;
}

