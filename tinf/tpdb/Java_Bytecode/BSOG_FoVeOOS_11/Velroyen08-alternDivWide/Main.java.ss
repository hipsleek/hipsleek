

data Main
{

}
 void Main_main(String[] args)
{
  AlternDivWide_loop(args.length);
}



data AlternDivWide
{

}
 void AlternDivWide_loop(int i)
{
  int w = 5;
  while (i != 0) {
    if (i < -w) {
      i--;
      i = i * -1;
    } else {
      if (i > w) {
        i++;
        i = i * -1;
      } else {
        i = 0;
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