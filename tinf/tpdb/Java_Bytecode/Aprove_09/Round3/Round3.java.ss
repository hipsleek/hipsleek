

data Round3
{

}
 void Round3_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  while (x % 3 != 0) {
    x++;
  }
}


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

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;