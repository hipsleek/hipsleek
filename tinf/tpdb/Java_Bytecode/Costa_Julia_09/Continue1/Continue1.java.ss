

data Continue1
{

}
 void Continue1_main(String[] args)
{
  int i = 0;
  while (i < 20) {
    i++;
    if (i <= 10)
      continue;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;