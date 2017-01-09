

data Loop
{

}
 void Loop_main(String[] args)
{
  int a = 5;
  int b = 3;
  
  int i = 0;
  while (i < 10) {
    i += 0;
  }
  
  Loop_test(a, b);
}

int Loop_test(int a, int b)
{
  return a * b;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;