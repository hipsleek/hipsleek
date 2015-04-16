

data NarrowKonv
{

}
 void NarrowKonv_loop(int i)
{
  int range = 20;
  while (0 <= i && i <= range) {
    if (!(0 == i && i == range)) {
      if (i == range) {
        i = 0;
        range--;
      } else {
        i++;
      }
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  NarrowKonv_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;