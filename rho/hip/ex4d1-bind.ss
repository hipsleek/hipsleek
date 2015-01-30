/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int val;
}

  
void main()
  requires emp ensures emp;
{
  cell x, y;
  x = new cell(1); 
  int r1,r2;
  par {r1,x@L}
  {  
  case {x@L,r1} x'::cell<n> -> // TODO: Should return error here
      dprint;
      r1 = x.val; 
   ||
  case {x@L} x'::cell<n> -> 
    dprint;
      x.val = x.val+1;
  }
  dprint;
}

/*
# ex4d1.ss

# bind vars need to be given permissions

Last Proving Location: 1 File "ex4d1-bind.ss",Line:24,Col:11

ERROR: at ex4d1-bind.ss_24:11_24:16
Message: val_24_1390 does not have @lend/@full permission to read.


*/
