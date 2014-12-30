

data NO_10
{

}
 void NO_10_main(String[] args)
{
  int j = 100;
  
  int i = 0;
  while (i < j) {
    j++;
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