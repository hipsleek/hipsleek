//#include "sl.h"
//#include <stdlib.h>

typedef struct item_t {
  int val;
  struct item_t *next;
} Item ;


void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;



Item* foo ()
/*@
   requires true
   ensures res != null;
*/
{
  Item* ptr = malloc(1);
  return ptr;
}
