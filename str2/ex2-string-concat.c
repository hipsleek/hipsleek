#include <string.h>

char* a (char *s)
  /*@
    requires true
    ensures slen(res)=3 ;
  */
{
  s = "abc";
  return s;
}

