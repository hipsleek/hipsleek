
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



data PastaB1
{

}
 void PastaB1_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  while (x > y) {
    x--;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;