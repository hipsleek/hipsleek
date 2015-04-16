

data Choose
{

}
 void Choose_main(String[] args)
{
  int i = 3;
  while (i >= 3) {
    if (i > 5)
      i += 3;
    else if (i > 10)
      i -= 2;
    else
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