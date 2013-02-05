//#include "sl.h"
//#include <stdlib.h>

typedef struct item_t {
  struct item_t *next;
} Item ;

void* malloc(int size) __attribute__ ((noreturn))
/*@
  requires size > 0
  ensures res != null;
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
