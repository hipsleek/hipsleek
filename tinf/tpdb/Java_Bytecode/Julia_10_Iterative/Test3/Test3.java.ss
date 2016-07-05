

data Test3
{

}
 void Test3_main(String[] args)
{
  List l1 = List_mk(args.length);
  List l2 = List_mk(args.length);
  List l3 = args.length % 2 == 0 ? List_mk(args.length * args.length) : l2;
  while (Test3_length(l1) + Test3_length(l2) + Test3_length(l3) * 5 > 0)
    if (Test3_length(l1) % 2 == 1)
      l1 = List_getTail();
    else if (Test3_length(l2) > Test3_length(l3))
      l2 = List_getTail();
    else if (l3 == null)
      break;
    else {
      l1 = new List(new Object(), l1);
      l2 = new List(new Object(), l2);
      l3 = List_getTail();
    }
}

int Test3_length(List list)
{
  int len = 0;
  while (list != null) {
    list = List_getTail();
    len++;
  }
  return len;
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