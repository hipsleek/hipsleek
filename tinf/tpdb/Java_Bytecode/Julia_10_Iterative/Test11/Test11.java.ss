

data Test11
{

}
 void Test11_main(String[] args)
{
  Random_args = args;
  int x = args.length * 100;
  int y = args.length * 200 / 13;
  while (x + y > 0) {
    if (Random_random() * Random_random() > 9)
      x--;
    else
      y--;
  }
}


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

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;