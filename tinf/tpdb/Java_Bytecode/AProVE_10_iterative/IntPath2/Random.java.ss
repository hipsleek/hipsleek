
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



data IntPath2
{

}
 void IntPath2_main(String[] args)
{
  Random_args = args;
  Object obj = null;
  int i = Random_random();
  if (i > 0)
    obj = new Object();
  while (i == 0 && obj != null)
    obj = new Object();
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;