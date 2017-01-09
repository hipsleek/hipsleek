/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Update x->car if x.
**/

//#include "slayer.h"

/*@
pred_prim memLoc<heap:bool,size:int>
  inv size>0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

typedef struct cell cell;
struct cell {
  int car;
  cell* cdr;
};

int main() {
  cell *x ;

  if (x) {
    x->car = x->car * 2 ;
    x->cdr = 0;
  }
  else {
    x = (cell*)malloc(sizeof(cell));
    x->car = 0;
  }

  return 0;
}
