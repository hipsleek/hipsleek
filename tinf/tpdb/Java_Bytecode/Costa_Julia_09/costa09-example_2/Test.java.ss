

data Test
{

}
 int Test_divBy(int x)
{
  int r = 0;
  int y;
  while (x > 0) {
    y = 2;
    x = x / y;
    r = r + x;
  }
  return r;
}

void Test_main(String[] args)
{
  if (args.length > 0) {
    int x = args[0]_length();
    int r = Test_divBy(x);
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;