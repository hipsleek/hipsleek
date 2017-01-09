

data NO_22
{

}
 void NO_22_main(String[] args)
{
  int i = 0;
  while (i < 100) {
    if (i < 50)
      i++;
    else
      i--;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;