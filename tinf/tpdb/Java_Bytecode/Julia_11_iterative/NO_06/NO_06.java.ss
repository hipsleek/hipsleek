

data NO_06
{

}
 void NO_06_main(String[] args)
{
  
  int i = 0;
  while (i < 100) {
    if (i < 0) {
      
      int j = 0;
      while (j < 15) {
        ;
        j++;
      }
      
      break;
    } else
      
      int j = 0;
      while (j < 15) {
        ;
        j += 0;
      }
      
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