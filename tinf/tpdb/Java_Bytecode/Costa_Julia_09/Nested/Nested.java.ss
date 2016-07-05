

data Nested
{

}
 void Nested_main(String[] args)
{
  
  int i = 0;
  while (i < 10) {
    
    int j = 3;
    while (j < 12) {
      j -= 1;
      j += 2;
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