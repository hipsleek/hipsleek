#include "sl.h"
//#include <stdlib.h>

int main() {
    struct item {
        struct item *next;
    } *ptr;

    ptr=NULL;
    for(;;) {
      void *data = ptr;
      ptr= malloc(sizeof *ptr);//new item
        if (!ptr)
            // OOM
            return -1;

        ptr->next = data;
        //   ___sl_plot("test-0001-snapshot");
    }
    return 0;
}

/*
pred_prim RS_mem<i:int>
 inv i>0 & self!=null;

RS_mem malloc(int n)
 requires n>0
 ensures  res=null or res::RS_mem<n>;

item cast_to_ptr(RS_mem p)
 case {
  p=null -> ensures res=null;
  p!=null -> 
    requires p::RS_mem<a> & a>=size(item)
    ensures res::item<_>
 }
*/
