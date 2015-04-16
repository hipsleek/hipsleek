

data WhileSum
{

}
 void WhileSum_increase(int i, int j)
{
  while (i + j > 0) {
    i++;
    if (j % 2 == 0) {
      j = j - 2;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  WhileSum_increase(args[0]_length(), args[1]_length());
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;