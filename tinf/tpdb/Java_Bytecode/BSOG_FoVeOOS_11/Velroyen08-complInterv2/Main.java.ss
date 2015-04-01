

data Main
{

}
 void Main_main(String[] args)
{
  ComplInterv2_loop(args.length);
}



data ComplInterv2
{

}
 void ComplInterv2_loop(int i)
{
  while (i != 0) {
    if (i > -5 && i < 5) {
      if (i < 0) {
        i++;
      }
      if (i > 0) {
        i--;
      }
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