

data Exc4
{

}
 void Exc4_main(String[] args)
{
  int i = 0;
  while (i < 20) {
    i--;
    try {
      if (i > 10)
        throw null;
      i += 2;
    } catch (NullPointerException e) {
      i++;
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