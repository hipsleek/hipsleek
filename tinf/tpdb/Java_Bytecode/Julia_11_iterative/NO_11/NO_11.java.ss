

data NO_11
{

}
 void NO_11_main(String[] args)
{
  int j = 100;
  
  int i = 0;
  while (i < j) {
    if (i < j - 2)
      continue;
    if (i > j - 2)
      break;
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