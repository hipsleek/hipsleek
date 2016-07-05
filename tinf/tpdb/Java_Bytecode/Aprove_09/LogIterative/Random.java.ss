
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



data LogIterative
{

}
 int LogIterative_log(int x, int y)
{
  int __res = 0;
  while (x >= y && y > 1) {
    __res++;
    x = x / y;
  }
  return __res;
}

void LogIterative_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  LogIterative_log(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;