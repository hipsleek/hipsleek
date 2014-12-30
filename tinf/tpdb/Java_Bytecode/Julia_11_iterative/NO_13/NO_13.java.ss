

data NO_13
{

}
 void NO_13_main(String[] args)
{
  int j = 100;
  
  int i = 0;
  while (i < j) {
    if (51 < j) {
      i++;
      j--;
    } else {
      i--;
      j++;
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