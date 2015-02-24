//#include "sl.h"
//#include <stdlib.h>

data item {
  int val;
  item_p next;
}

data item_p {
  item pdata;
}

pred_prim RS_mem<i:int>
  inv i>0 & self!=null;
 
RS_mem malloc(int n)
  requires n>0
  ensures res=null or res::RS_mem<n>;

item_p cast_to_ptr(RS_mem p)
  case {
    p=null -> ensures res=null;
    p!=null -> requires p::RS_mem<a> & a>=1
               ensures res::item_p<_>;
  }

item_p foo ()
  requires true
  ensures res::item_p<_>;
{
  item_p ptr;
  ptr = cast_to_ptr(malloc(1));
  if (ptr==null) {
    assume false;
  }
  return ptr;
}