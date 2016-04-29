#include <string.h>

char* a (char* s)
  /*@
    requires true
    ensures s'="ab"^"c";
  */
{
  //s = "abc";
  *s = 'a';
  s[1] = 'b';
  s[2] = 'c';
  s[3] = '\0';
  return s;
}

