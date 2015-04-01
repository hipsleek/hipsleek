

data NonPeriodic
{

}
 void NonPeriodic_main(String[] args)
{
  int x = 1;
  int y = 0;
  if (args.length >= 1) {
    y = -1 * args[0]_length();
  }
  while (y > 0)
    if (x > 0)
      x = x - 1;
    else {
      y = y + 1;
      x = y;
    }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;