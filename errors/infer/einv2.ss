relation H(int a).
relation H1(int a).

int xZero(int input)
  infer [H]
  requires H(input)
  ensures res!=0;
{
  int x = 1;
  int y = input - 42;

  if (y<0){
    x=0;
  }
  return x;
}


int neg_xZero(int input)
  infer [H1]
  requires H1(input)
  ensures res=0;
{
  int x = 1;
  int y = input - 42;

  if (y<0){
    x=0;
  }
  return x;
}

int yZero(int input)
  infer [H1]
  requires H1(input)
  ensures res=0;
{
  int x = 0;
  int y = input - 42;

  if (y<0){
    y=0;
  }
  return x;
}
