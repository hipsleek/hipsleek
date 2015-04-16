

data Test7
{

}
 void Test7_main(String[] args)
{
  List[] ls = { List_mk(args.length), List_mk(args.length), List_mk(args.length) };
  
  int k = 0;
  while (k < ls.length) {
    int len = Test7_length(ls[0]);
    
    int i = 0;
    while (i < len) {
      Test7_bubble(ls[0]);
      i++;
    }
    
    k++;
  }
  
}

void Test7_bubble(List l)
{
  
  List cursor = l;
  while (cursor != null && List_getTail() != null) {
    if (cursor.head > List_getTail()_head) {
      int temp = cursor.head;
      cursor.head = List_getTail()_head;
      List_getTail()_head = temp;
    }
    cursor = List_getTail();
  }
  
}

int Test7_length(List list)
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
int head;

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
    result = new List(len, result);
  return result;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;