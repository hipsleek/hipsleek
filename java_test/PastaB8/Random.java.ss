
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



data PastaB8
{

}
 void PastaB8_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  if (x > 0) {
    while (x != 0) {
      if (x % 2 == 0) {
        x = x / 2;
      } else {
        x--;
      }
    }
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;