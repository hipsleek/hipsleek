
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



data ListContentTail
{

}
 void ListContentTail_main(String[] args)
{
  Random_args = args;
  IntList l = IntList_createIntList();
  int m = IntList_nth(Random_random(), l);
  while (m > 0) {
    l = l.next;
    m = IntList_nth(Random_random(), l);
  }
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

int IntList_nth(int n, IntList l)
{
  while (n > 1 && l != null) {
    n--;
    l = l.next;
  }
  if (l == null)
    return 0;
  else
    return l.value;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;