

data Swingers
{

}
 void Swingers_main(String[] args)
{
  int bob = 13;
  int samantha = 17;
  while (bob + samantha < 100) {
    int temp = bob;
    bob = samantha;
    samantha = temp;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;