

data NonPeriodicNonterm2
{

}
 void NonPeriodicNonterm2_main(String[] args)
{
  int x = args[0]_length();
  int y = args[1]_length();
  while (x >= y) {
    int z = x - y;
    if (z > 0) {
      x--;
    } else {
      x = 2 * x + 1;
      y++;
    }
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;