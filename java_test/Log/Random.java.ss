
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



data Log
{

}
 int Log_half(int x)
{
  int __res = 0;
  while (x > 1) {
    x = x - 2;
    __res++;
  }
  return __res;
}

int Log_log(int x)
{
  int __res = 0;
  while (x > 1) {
    x = Log_half(x);
    __res++;
  }
  return __res;
}

void Log_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  Log_log(x);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;