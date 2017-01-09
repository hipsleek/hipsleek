

data RetVal
{

}
 void RetVal_main(String[] args)
{
  Random_args = args;
  int x = Random_random() % 2;
  int y = RetVal_ret(x);
  RetVal_test(x, y);
}

int RetVal_ret(int x)
{
  if (x == 0)
    return 1;
  else
    return 0;
}

boolean RetVal_test(int x, int y)
{
  while (x == y) {
    x--;
    y--;
  }
  return true;
}


global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;