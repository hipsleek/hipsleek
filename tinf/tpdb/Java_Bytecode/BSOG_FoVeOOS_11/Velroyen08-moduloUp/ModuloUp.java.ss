

data ModuloUp
{

}
 void ModuloUp_up(int n)
{
  int d = 10;
  while (n < 15) {
    n++;
    n = n % d;
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  ModuloUp_up(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;