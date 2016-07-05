
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  if (Random_index >= Random_args.length)
    return 0;
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data Et1
{

}
 void Et1_main(String[] args)
{
  Random_args = args;
  int a = -Random_random();
  int b = -Random_random();
  while (a > b) {
    b = b + a;
    a = a + 1;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;