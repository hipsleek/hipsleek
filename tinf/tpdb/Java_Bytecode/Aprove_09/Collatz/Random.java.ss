
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



data Collatz
{

}
 void Collatz_main(int x)
{
  int n = x;
  while (n > 1) {
    if (n % 2 == 0) {
      n = n / 2;
    } else {
      n = 3 * n + 1;
    }
  }
}

void Collatz_main(String[] args)
{
  Random_args = args;
  Collatz_main(Random_random());
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;