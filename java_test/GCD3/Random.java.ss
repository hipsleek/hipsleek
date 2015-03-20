
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



data GCD3
{

}
 int GCD3_mod(int a, int b)
{
  if (b == 0) {
    return b;
  }
  if (b < 0) {
    a = -a;
  }
  if (a > 0) {
    while (a >= b) {
      a -= b;
    }
    return a;
  } else {
    while (a < 0) {
      a -= b;
    }
    return a;
  }
}

int GCD3_gcd(int a, int b)
{
  int tmp;
  while (b > 0 && a > 0) {
    tmp = b;
    b = GCD3_mod(a, b);
    a = tmp;
  }
  return a;
}

void GCD3_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  GCD3_gcd(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;