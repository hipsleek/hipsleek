

data Main
{

}
 void Main_main(String[] args)
{
  ComplInterv_loop(args.length);
}



data ComplInterv
{

}
 void ComplInterv_loop(int i)
{
  while (i * i > 9) {
    if (i < 0) {
      i = i - 1;
    } else {
      i = i + 1;
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