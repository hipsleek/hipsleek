

data SortCount
{

}
 void SortCount_main(String[] args)
{
  Random_args = args;
  IntList l = IntList_createIntList();
  l = IntList_sort(0, l);
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

boolean IntList_member(int n, IntList l)
{
  while (l != null) {
    if (l.value == n)
      return true;
    else
      l = l.next;
  }
  return false;
}

int IntList_max(IntList l)
{
  int m = 0;
  while (l != null) {
    if (l.value > m)
      m = l.value;
    l = l.next;
  }
  return m;
}

IntList IntList_sort(int n, IntList l)
{
  IntList __res = null;
  while (IntList_max(l) >= n) {
    if (IntList_member(n, l))
      __res = new IntList(n, __res);
    n++;
  }
  return __res;
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