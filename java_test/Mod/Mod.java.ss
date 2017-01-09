

data Mod
{

}
 void Mod_main(String[] args)
{
  int x = args[0]_length();
  int y = args[1]_length();
  Mod_mod(x, y);
}

int Mod_mod(int x, int y)
{
  while (x >= y && y > 0) {
    x = Mod_minus(x, y);
  }
  return x;
}

int Mod_minus(int x, int y)
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

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;