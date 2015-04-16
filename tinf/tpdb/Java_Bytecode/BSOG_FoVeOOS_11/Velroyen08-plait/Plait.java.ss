

data Plait
{

}
 void Plait_loop(int i, int j, int k)
{
  int plaitNext = 0;
  int swap = 0;
  while (i > 0 || j > 0 || k > 0) {
    if (plaitNext == 0) {
      swap = i;
      i = j / 2;
      j = swap * 2;
      plaitNext = 1;
    } else {
      swap = k;
      k = j * 2;
      j = swap / 2;
      plaitNext = 0;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  Plait_loop(args[0]_length(), args[1]_length(), args[2]_length());
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;