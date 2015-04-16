

data Marbie1
{

}
 void Marbie1_loop(int i)
{
  while (i > 2) {
    i++;
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  Marbie1_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;