

data NO_24
{

}
 void NO_24_main(String[] args)
{
  int a = 1;
  int b = 2;
  while (a + b < 5) {
    a = a - b;
    b = a + b;
    a = b - a;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;