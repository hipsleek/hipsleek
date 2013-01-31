#include "sl.h"
//#include <stdlib.h>

typedef struct item_t {
     struct item_t *next;
} Item ;


Item* foo ()
/*@
   requires true
   ensures res::item<_>;
*/
{
  Item* ptr;
  ptr = malloc(sizeof *ptr);
  if (!ptr) {
    //@ assume false;
  }
  return ptr;   
}

void main() {

}

