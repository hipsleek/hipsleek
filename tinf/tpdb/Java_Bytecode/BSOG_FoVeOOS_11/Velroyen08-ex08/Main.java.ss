

data Main
{

}
 void Main_main(String[] args)
{
  Ex08_loop(args.length);
}



data Ex08
{

}
 void Ex08_loop(int i)
{
  boolean up = false;
  while (i > 0) {
    if (i == 1) {
      up = true;
    }
    if (i == 10) {
      up = false;
    }
    if (up) {
      i++;
    } else {
      i--;
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