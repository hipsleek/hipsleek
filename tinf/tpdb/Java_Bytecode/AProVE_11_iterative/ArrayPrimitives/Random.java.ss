
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



data ArrayPrimitives
{

}
 void ArrayPrimitives_main(String[] argv)
{
  Random_args = argv;
  int int0 = Random_random();
  int int1 = Random_random();
  int int2 = Random_random();
  int[] data = { int0, int1, int2 };
  while (data[0] != int0)
    ;
  while (data[1] != int1)
    ;
  while (data[2] != int2)
    ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;