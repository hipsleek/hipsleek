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
  if (rand()) x=new cell(5);
  return x.val;
}

/*
# ex1-null.ss




*/
