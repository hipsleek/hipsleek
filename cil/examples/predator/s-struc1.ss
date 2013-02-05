//#include "sl.h"
//#include <stdlib.h>

data memory {
  int size;
}
 
data item {
  int val;
  item next;
}
 
memory malloc(int size)
  requires size>0
  ensures  res=null or res::memory<size>;
{
}

item cast_to_ptr(memory p)
  case {
    p=null -> ensures res=null;
    p!=null -> 
      requires p::memory<size> & size>=1
      ensures res::item<_,_>;
  }

item foo ()
  requires true
  ensures res::item<_,_>;
{
  item ptr;
  ptr = /*@ (item) */ cast_to_ptr(malloc(1));
  if (ptr==null) {
    assume false;
  }
  return ptr;   
}



