
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



data ListContentArbitrary
{

}
 void ListContentArbitrary_main(String[] args)
{
  Random_args = args;
  IntList l = IntList_createIntList();
  int n = Random_random();
  int m = IntList_nth(n);
  while (m > 0)
    m--;
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

int IntList_nth(IntList _this, int n)
{
  IntList l = this;
  while (n > 1) {
    n--;
    l = l.next;
  }
  return l.value;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;