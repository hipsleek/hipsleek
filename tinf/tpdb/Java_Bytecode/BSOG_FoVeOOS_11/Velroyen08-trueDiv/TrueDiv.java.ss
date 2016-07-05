

data TrueDiv
{

}
 void TrueDiv_loop(int i)
{
  while (true) {
    if (i <= 0) {
      i--;
    } else {
      i++;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  TrueDiv_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;