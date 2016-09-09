//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

// ../hip ex1a-alloca-while.c -infer "@shape_prepost@term"
data cell{
  int val;
}

void loop (cell y)
  infer[@shape_prepost]
  requires true
  ensures true;
{
    while (y.val > 0) 
    infer[@shape_prepost]
    requires true
    ensures true;
   {
      y.val = y.val - 1;
    }
}


/*
# ex1a5a.ss

# No split-component problem here ..

*/
