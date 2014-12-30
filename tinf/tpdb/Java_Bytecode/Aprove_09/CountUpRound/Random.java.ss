
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



data CountUpRound
{

}
 int CountUpRound_round(int x)
{
  if (x % 2 == 0)
    return x;
  else
    return x + 1;
}

void CountUpRound_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  while (x > y) {
    y = CountUpRound_round(y + 1);
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;