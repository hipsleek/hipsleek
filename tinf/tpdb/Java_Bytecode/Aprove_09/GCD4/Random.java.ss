
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



data GCD4
{

}
 int GCD4_mod(int a, int b)
{
  while (a >= b && b > 0) {
    a -= b;
  }
  return a;
}

int GCD4_gcd(int a, int b)
{
  int tmp;
  while (b > 0 && a > 0) {
    tmp = b;
    b = GCD4_mod(a, b);
    a = tmp;
  }
  return a;
}

void GCD4_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  GCD4_gcd(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;