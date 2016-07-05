

data Sunset
{

}
 void Sunset_loop(int i)
{
  while (i > 10) {
    if (i == 25) {
      i = 30;
    }
    if (i <= 30) {
      i--;
    } else {
      i = 20;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  Sunset_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;