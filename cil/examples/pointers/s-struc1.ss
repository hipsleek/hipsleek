//#include "sl.h"
//#include <stdlib.h>

data memory {
  int val;
  memory next;
}
 
data item {
  int val;
  item next;
}
 
memory malloc(int size)
  case {
    size <= 0 -> requires true ensures res =  null;
    size >  0 -> requires true ensures res != null;
  }

item cast_to_ptr(memory p)
  case {
    p =  null -> ensures res =  null;
    p != null -> ensures res::item<_>;
  }

item foo ()
  requires true
  ensures res::item<_,_>;
{
  item ptr;
  ptr = cast_to_ptr(malloc(1));
  if (ptr == null) {
    assume false;
  }
  return ptr;   
}



