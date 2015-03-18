data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

void free(cell x)
 requires x::cell<_>
 ensures emp;

int foo()
  requires true
  ensures true;
{
  cell x;
  x=new cell(5);
  int r=x.val;
  free(x);
  free(x);
  return r;
}


