#include <string.h>

void a (char *s)
  /*@
    requires true
    ensures s="abc";
  */
{
  s = "abc";
}

