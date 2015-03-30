
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



data Et6
{

}
 void Et6_main(String[] args)
{
  Random_args = args;
  int a = Random_random();
  int b = Random_random();
  int c = Random_random();
  while (c >= 0) {
    int ap = Random_random();
    int bp = Random_random();
    if (3 * b - 2 * a >= 3 * bp - 2 * ap)
      break;
    a = ap;
    b = bp;
    c = c - (3 * b - 2 * a);
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;