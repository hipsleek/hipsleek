

data Exc
{
int f;
}
 void Exc_main(String[] args)
{
  Exc exc = new Exc();
  int i = 0;
  while (i < 20) {
    try {
      if (i > 10)
        exc.f = 5;
      i += 2;
    } catch (NullPointerException e) {
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