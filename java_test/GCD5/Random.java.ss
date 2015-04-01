
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



data GCD5
{

}
 int GCD5_gcd(int a, int b)
{
  int tmp;
  while (b > 0 && a > 0) {
    tmp = b;
    b = a % b;
    a = tmp;
  }
  return a;
}

void GCD5_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  GCD5_gcd(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;