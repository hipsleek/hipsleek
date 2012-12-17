
//#include "sl.h"
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
    //for()  {
        data = ptr;
        //  ptr = malloc(4);//new item
        if (ptr==null)
            // OOM
            return -1;

        ptr.next = data;
        //   ___sl_plot("test-0001-snapshot");
        //}
    return 0;
}

