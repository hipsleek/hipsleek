/* Example with simple CountDownLatch */

//CountDownLatch

data cell { int val; }


/********************************************/
int foo(cell h)
  requires h::cell<n> * @frac(1/2)[h]
  ensures res=n+1;
{
  int r = h.val;
  return r+1;
}

/*
# ex11b1.ss --ann-vp

This example should fail but is not
 State:h::cell<n>&MayLoop[] & h'=h&{FLOW,(4,5)=__norm#E}[]


*/
