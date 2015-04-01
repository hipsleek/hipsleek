
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



data DivMinus
{

}
 int DivMinus_div(int x, int y)
{
  int __res = 0;
  while (x >= y && y > 0) {
    x = x - y;
    __res = __res + 1;
  }
  return __res;
}

void DivMinus_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  DivMinus_div(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;