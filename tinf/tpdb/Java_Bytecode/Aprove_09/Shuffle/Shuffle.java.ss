

data Shuffle
{

}
 void Shuffle_main(String[] args)
{
  Random_args = args;
  IntList l = IntList_createIntList();
  IntList __res = null;
  while (l != null) {
    __res = new IntList(l.value, __res);
    l = l.next;
    if (l != null)
      l = IntList_reverse();
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
  int j;
  IntList l = null;
  while (i > 0) {
    j = Random_random();
    l = new IntList(j, l);
    i--;
  }
  return l;
}

IntList IntList_reverse(IntList _this)
{
  IntList __res = null;
  IntList l = this;
  while (l != null) {
    __res = new IntList(l.value, __res);
    l = l.next;
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