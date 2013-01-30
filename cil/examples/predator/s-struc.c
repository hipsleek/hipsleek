//#include "sl.h"
#include <stdlib.h>

typedef struct item {
     struct item *next;
} titem ;


titem* foo ()
/*@
   requires true
   ensures res::item<_>;
*/
{
  titem* ptr;
  ptr = malloc(sizeof *ptr);
  if (!ptr) {
    //@ assume false;
  }
  return ptr;   
}

void main() {

}

