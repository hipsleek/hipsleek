#include "sl.h"
//#include <stdlib.h>

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

int main() {
    struct item {
        struct item *next;
    } *ptr;

    ptr=NULL;
    for(;;) {
      void *data_ = ptr;
      ptr= malloc(sizeof *ptr);//new item
        if (!ptr)
            // OOM
            return -1;

        ptr->next = data_;
        //   ___sl_plot("test-0001-snapshot");
    }
    return 0;
}

/*

*/
