

data Main
{

}
 void Main_main(String[] args)
{
  ConvLower_loop(args.length);
}



data ConvLower
{

}
 void ConvLower_loop(int i)
{
  while (i > 5) {
    if (i != 10) {
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