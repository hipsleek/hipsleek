
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



data LogMult
{

}
 int LogMult_log(int x, int y)
{
  int __res = 1;
  if (x < 0 || y < 1)
    return 0;
  else {
    while (x > y) {
      y = y * y;
      __res = 2 * __res;
    }
  }
  return __res;
}

void LogMult_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  LogMult_log(x, 2);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;