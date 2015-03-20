

data Continue
{

}
 void Continue_main(String[] args)
{
  int i = 0;
  while (i < 20) {
    if (i <= 10)
      continue;
    i++;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;