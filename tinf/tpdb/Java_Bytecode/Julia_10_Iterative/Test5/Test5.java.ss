

data Test5
{

}
 void Test5_main(String[] args)
{
  List l1 = List_mk(args.length);
  List l2 = List_mk(args.length + 3);
  List l3 = List_mk(args.length + 5);
  List temp;
  while (Test5_length(l1) > 0) {
    temp = l1;
    l1 = l2;
    l2 = l3;
    l3 = temp;
    if (Test5_length(l2) % 3 == 0)
      temp = List_getTail();
    if (Test5_length(l3) % 5 == 0)
      l3 = List_getTail();
    if (Test5_length(l1) > Test5_length(l2))
      l1 = List_getTail();
    else if (Test5_length(l1) == Test5_length(l2))
      l2 = List_getTail();
    else
      l3 = List_getTail();
    Test5_test(l1, l2, l3);
  }
}

int Test5_length(List list)
{
  int len = 0;
  while (list != null) {
    list = List_getTail();
    len++;
  }
  return len;
}

void Test5_test(List l1, List l2, List l3)
{
  while (l1 != null) {
    l2 = new List(l1, l2);
    l3 = new List(l2, l3);
    l1 = List_getTail();
  }
}



data List
{
Object head;

List tail;
}
 List List_getTail(List _this)
{
  return _this.tail;
}

List List_mk(int len)
{
  List result = null;
  while (len-- > 0)
    result = new List(new Object(), result);
  return result;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;