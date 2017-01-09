data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

bool goo(cell x)
  requires x!=null
  ensures true;

int foo()
  requires true
  ensures true;
{
  cell x;
  //goo(x);
  if (rand()) x=new cell(5);
  return x.val;
}

