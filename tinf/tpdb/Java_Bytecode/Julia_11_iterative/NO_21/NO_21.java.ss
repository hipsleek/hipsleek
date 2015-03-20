

data NO_21
{

}
 void NO_21_main(String[] args)
{
  int i = 0;
  while (i < 100) {
    i++;
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