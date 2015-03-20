
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



data B
{

}
 void B_method(B _this)
{
  return;
}



data ArrayClasses
{

}
 void ArrayClasses_main(String[] args)
{
  Random_args = args;
  A[] data = new A[2];
  data[0] = new A();
  data[1] = new B();
  int i = Random_random();
  if (i == 1)
    data[i]_method();
}



data A
{

}
 void A_method(A _this)
{
  while (true)
    ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;