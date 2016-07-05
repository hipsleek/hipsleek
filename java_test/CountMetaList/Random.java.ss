
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



data CountMetaList
{

}
 void CountMetaList_main(String[] args)
{
  Random_args = args;
  List l = CountMetaList_createMetaList();
  int count = CountMetaList_countMetaList(l);
}

int CountMetaList_countMetaList(List cur)
{
  int __res = 0;
  while (cur != null) {
    if (cur.value instanceof List) {
      List inner = (List)cur.value;
      cur.value = inner.next;
      cur = new List(inner.value, cur);
    }
    cur = cur.next;
    __res++;
  }
  return __res;
}

List CountMetaList_createMetaList()
{
  int count = Random_random();
  List cur = null;
  for (int i = 0; CountMetaList_i < count; CountMetaList_i++) {
    int innerCount = Random_random();
    List innerList = null;
    for (int j = innerCount; CountMetaList_j > 0; CountMetaList_j--) {
      innerList = new List(null, innerList);
    }
    cur = new List(innerList, cur);
  }
  return cur;
}



data List
{
Object value;

List next;
}
 

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;