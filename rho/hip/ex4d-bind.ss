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
  par {r1,r2,x@L}
  {  
  case {x@L,r2} x'::cell<n>@L -> 
    r2 = x.val+1;
    dprint;
  ||
  case {x@L,r1} x'::cell<n>@L -> // TODO: Should return error here
      r1 = x.val; 
      dprint;
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
