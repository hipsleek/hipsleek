

data WhileTrue
{

}
 void WhileTrue_endless(int i)
{
  while (true) {
    i++;
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  WhileTrue_endless(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;