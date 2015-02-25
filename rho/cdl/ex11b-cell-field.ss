/* Example with simple CountDownLatch */

//CountDownLatch

data cell { int val; }


/********************************************/
int foo(cell h)
  requires h::cell<n>
  ensures res=n+1;
{
  dprint;
  int r = h.val;
  cell c = h;
  //Message: h does not have @lend/@full permission to read.
  dprint;
  return r+1;
}

/*
# ex11b.ss --ann-vp

This example should fail but is not
 State:h::cell<n>&MayLoop[] & h'=h&{FLOW,(4,5)=__norm#E}[]


*/
