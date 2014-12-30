

data Main
{

}
 void Main_main(String[] args)
{
  AlternKonv_loop(args.length);
}



data AlternKonv
{

}
 void AlternKonv_loop(int i)
{
  while (i != 0) {
    if (i < 0) {
      i = i + 2;
      if (i < 0) {
        i = i * -1;
      }
    } else {
      i = i - 2;
      if (i > 0) {
        i = i * -1;
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