
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  if (Random_index >= Random_args.length)
    return 0;
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data Et5
{

}
 void Et5_main(String[] args)
{
  Random_args = args;
  int a = Random_random();
  int b = Random_random();
  int c = Random_random();
  while (c >= 0) {
    int ap = Random_random();
    int bp = Random_random();
    if (2 * a - b <= 2 * ap - bp)
      break;
    a = ap;
    b = bp;
    c = c + 2 * a - b;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;