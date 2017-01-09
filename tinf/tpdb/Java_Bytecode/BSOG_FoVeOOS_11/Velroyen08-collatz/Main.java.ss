

data Main
{

}
 void Main_main(String[] args)
{
  Collatz_collatz(args.length);
}



data Collatz
{

}
 void Collatz_collatz(int i)
{
  while (i > 1) {
    if (i % 2 == 0) {
      i = i / 2;
    } else {
      i = 3 * i + 1;
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