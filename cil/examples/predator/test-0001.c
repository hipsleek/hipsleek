#include "sl.h"
//#include <stdlib.h>

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
