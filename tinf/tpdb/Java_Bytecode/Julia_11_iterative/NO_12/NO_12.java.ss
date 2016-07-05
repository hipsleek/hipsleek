

data NO_12
{

}
 void NO_12_main(String[] args)
{
  int j = 0;
  
  int i = 0;
  while (i <= j) {
    if (j - i < 1)
      j += 2;
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