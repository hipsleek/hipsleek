//#include "sl.h"
//#include <stdlib.h>

typedef struct item_t {
  struct item_t *next;
} Item ;


Item* foo ()
/*@
   requires true
   ensures res != null;
*/
{
  Item* ptr = cast_to_ptr(malloc(1));
  return ptr;
}
