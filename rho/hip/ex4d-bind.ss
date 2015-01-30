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
      //r1 = x.val; 
   ||
  case {x@L} x'::cell<n> -> 
    dprint;
      x.val = x.val+1;
  }
  dprint;
}

/*
# ex4d.ss

What lexvar error is this?


Last Proving Location: 1 File "ex4d-bind.ss",Line:18,Col:6

ERROR: at _0:0_0:0
Message: [term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped.




*/
