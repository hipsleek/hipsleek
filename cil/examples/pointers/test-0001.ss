
data item {
       item next;
    }
/*

//#include "sl.h"
    requires p::RS_mem<a> //& a>=size(item)
    ensures res::item<_>;
*/

// #include "sl.h"
//#include <stdlib.h>
data item {
        item next;
    }

int main()
  requires true
  ensures true;
 {
    item ptr;
  item data;
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

