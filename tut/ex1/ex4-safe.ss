data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

int foo()
  requires true
  ensures true;
{
  cell x;
  x=new cell(5);
  return x.val;
}
