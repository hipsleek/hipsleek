
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



data IntRTA
{
int val;
}
 void IntRTA_count(IntRTA orig, IntRTA limit)
{
  if (orig == null || limit == null) {
    return;
  }
  IntRTA copy = orig;
  while (orig.val < limit.val) {
    copy.val++;
  }
}

void IntRTA_main(String[] args)
{
  Random_args = args;
  IntRTA x = new IntRTA();
  x.val = Random_random();
  IntRTA y = new IntRTA();
  y.val = Random_random();
  IntRTA_count(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;