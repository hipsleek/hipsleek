data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

int foo()
  infer [@leak]
  requires emp  ensures emp;
{
  cell x;
  x=new cell(5);
  return x.val;
}

