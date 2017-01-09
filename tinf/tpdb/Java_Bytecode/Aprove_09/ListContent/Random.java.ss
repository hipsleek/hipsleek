
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



data ListContent
{

}
 void ListContent_main(String[] args)
{
  Random_args = args;
  IntList l = IntList_createIntList();
  while (l.value > 0)
    l.value--;
}



data IntList
{
int value;

IntList next;
}
 IntList IntList_createIntList()
{
  int i = Random_random();
  IntList l = null;
  while (i > 0) {
    l = new IntList(Random_random(), l);
    i--;
  }
  return l;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;