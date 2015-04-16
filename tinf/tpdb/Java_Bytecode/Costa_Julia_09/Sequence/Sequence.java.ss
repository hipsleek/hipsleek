

data Sequence
{

}
 void Sequence_main(String[] args)
{
  
  int i = 0;
  while (i < 100) {
    i++;
  }
  
  ;
  
  int j = 5;
  while (j < 21) {
    j += 3;
  }
  
  ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;