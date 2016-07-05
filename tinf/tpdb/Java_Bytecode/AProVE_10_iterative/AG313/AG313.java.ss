

data AG313
{

}
 void AG313_main(String[] args)
{
  int x;
  int y;
  x = args[0]_length();
  y = args[1]_length() + 1;
  AG313_quot(x, y);
}

int AG313_quot(int x, int y)
{
  int i = 0;
  if (x == 0)
    return 0;
  while (x > 0 && y > 0) {
    i += 1;
    x = x - 1 - (y - 1);
  }
  return i;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;