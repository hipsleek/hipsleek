
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



data NullPair
{
NullPair next;
}
 void NullPair_main(String[] args)
{
  Random_args = args;
  NullPair one = null;
  NullPair two = null;
  int i = Random_random();
  if (i == 0) {
    one = new NullPair();
  } else {
    two = new NullPair();
  }
  while (one == null && two == null)
    ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;