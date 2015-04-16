

data Main
{

}
 void Main_main(String[] args)
{
  Ex04_loop(args.length);
}



data Ex04
{

}
 void Ex04_loop(int i)
{
  while (true) {
    i--;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;