
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



data PastaC7
{

}
 void PastaC7_main(String[] args)
{
  Random_args = args;
  int i = Random_random();
  int j = Random_random();
  int k = Random_random();
  while (i <= 100 && j <= k) {
    int t = i;
    i = j;
    j = i + 1;
    k--;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;