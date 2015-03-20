
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



data MinusUserDefined
{

}
 boolean MinusUserDefined_gt(int x, int y)
{
  while (x > 0 && y > 0) {
    x--;
    y--;
  }
  return x > 0;
}

void MinusUserDefined_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  int __res = 0;
  while (MinusUserDefined_gt(x, y)) {
    y++;
    __res++;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;