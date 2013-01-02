
data item {
       item next;
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
    requires p::RS_mem<a> //& a>=size(item)
    ensures res::item<_>;
 }
*/


// #include "sl.h"
//#include <stdlib.h>

int main()
  requires true
  ensures true;
 {
    item ptr;
    ptr=null;
    while (true) {
    //  void *data = ptr;
      item data_;
      ptr = cast_to_ptr(malloc(4));//new item
      if (ptr == null)
          // OOM
        //return -1;

      ptr.next = data_;
      //   ___sl_plot("test-0001-snapshot");
    };
    return 0;
}

