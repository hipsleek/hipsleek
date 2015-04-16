

data Main
{

}
 void Main_main(String[] args)
{
  int value = args[1]_length();
  if (args[0]_length() % 2 == 0) {
    value = -value;
  }
  Ex06_loop(value);
}



data Ex06
{

}
 void Ex06_loop(int i)
{
  while (i >= -5 && i <= 5) {
    if (i > 0) {
      i--;
    }
    if (i < 0) {
      i++;
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