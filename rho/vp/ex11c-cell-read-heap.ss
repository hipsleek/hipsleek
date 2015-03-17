/* Example with simple CountDownLatch */

//CountDownLatch

data cell { int val; }


/********************************************/
int foo(cell h)
  requires h::cell<n>
  ensures res=1;
{
  //dprint;
  cell c = h;
  //Message: h does not have @lend/@full permission to read.
  dprint;
  return 1;
}

/*
# ex11c.ss --ann-vp

This example correctly fails ..

 State:h::cell<n>&MayLoop[] & h'=h&{FLOW,(4,5)=__norm#E}[]

Exception Failure("h does not have @lend/@full permission to read.") Occurred!


*/
