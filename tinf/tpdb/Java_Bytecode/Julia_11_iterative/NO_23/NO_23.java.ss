

data NO_23
{

}
 void NO_23_main(String[] args)
{
  int i = 0;
  while (i < 100) {
    if (i < 50)
      i = 51;
    else
      i = 49;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;