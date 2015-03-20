

data WhileIncrPart
{

}
 void WhileIncrPart_increase(int i)
{
  while (i > 0) {
    if (i > 3) {
      i++;
    } else {
      i--;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  WhileIncrPart_increase(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;