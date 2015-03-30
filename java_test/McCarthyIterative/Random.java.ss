
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



data McCarthyIterative
{

}
 int McCarthyIterative_main(int x)
{
  int c = 1;
  while (c > 0) {
    if (x > 100) {
      x -= 10;
      c--;
    } else {
      x += 11;
      c++;
    }
  }
  return x;
}

void McCarthyIterative_main(String[] args)
{
  Random_args = args;
  McCarthyIterative_main(Random_random());
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;