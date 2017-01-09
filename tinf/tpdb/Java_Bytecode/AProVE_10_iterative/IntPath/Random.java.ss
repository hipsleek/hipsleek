
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



data IntPath
{

}
 void IntPath_main(String[] args)
{
  Random_args = args;
  int i = Random_random();
  int x = 0;
  int y = 0;
  if (i > 10) {
    x = 1;
  } else {
    y = 1;
  }
  while (x == y)
    ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;