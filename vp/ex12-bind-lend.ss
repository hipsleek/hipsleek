//CountDownLatch

data cell { int val; }


/********************************************/
int foo(cell h)
  requires h::cell<n> * @value[h]
  ensures res=n+1;
{
  int r;
  bind h to (v) // requires @L on h only
    in { h = null;
         r = v; };
  dprint;
  return r+1;
}

/*
# ex12.ss --ann-vp

seems @L on bind is good here as the idea is to read
and then immediately return any permission.

After that full permission is still in place
for h to be assigned to null.

*/
