

data ArrayObjects
{

}
 void ArrayObjects_main(String[] argv)
{
  Object obj0 = new Object();
  Object obj1 = new Object();
  Object obj2 = new Object();
  Object[] data = { obj0, obj1, obj2 };
  while (data[0] != obj0)
    ;
  while (data[1] != obj1)
    ;
  while (data[2] != obj2)
    ;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;