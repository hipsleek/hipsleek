
//#include "sl.h"
//#include <stdlib.h>
data item {
        item next;
    }

int main() {
    
    item ptr;
    ptr=null;
    //for()  {
        void *data = ptr;
        ptr = malloc(sizeof *ptr);//new item
        if (!ptr)
            // OOM
            return -1;

        ptr->next = data;
        //   ___sl_plot("test-0001-snapshot");
        //}
    return 0;
}

