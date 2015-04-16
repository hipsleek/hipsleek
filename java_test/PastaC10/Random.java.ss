
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



data PastaC10
{

}
 void PastaC10_main(String[] args)
{
  Random_args = args;
  int i = Random_random();
  int j = Random_random();
  while (i - j >= 1) {
    i = i - Random_random();
    int r = Random_random() + 1;
    j = j + r;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;