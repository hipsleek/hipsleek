
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data DivMinus2
{

}
 int DivMinus2_div(int x, int y)
{
  int __res = 0;
  while (x >= y && y > 0) {
    x = DivMinus2_minus(x, y);
    __res = __res + 1;
  }
  return __res;
}

int DivMinus2_minus(int x, int y)
{
  while (y != 0) {
    if (y > 0) {
      y--;
      x--;
    } else {
      y++;
      x++;
    }
  }
  return x;
}

void DivMinus2_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  DivMinus2_div(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;