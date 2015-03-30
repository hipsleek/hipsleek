

data Main
{

}
 void Main_main(String[] args)
{
  AlternDiv_loop(args.length);
}



data AlternDiv
{

}
 void AlternDiv_loop(int i)
{
  while (i != 0) {
    if (i < 0) {
      i--;
      i = i * -1;
    } else {
      i++;
      i = i * -1;
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