
global List Test13_l1;

global List Test13_l2;
data Test13
{

}
 void Test13_main(String[] args)
{
  List l = new List(13, null);
  List start = l;
  
  int i = 0;
  while (i < args.length + 1) {
    l = l.tail = new List(11, null);
    i++;
  }
  
  Test13_l1 = l;
  Test13_l2 = start;
  Test13_test();
  Test13_length(start);
}

int Test13_length(List l)
{
  int length = 0;
  while (l != null) {
    l = l.tail;
    length++;
  }
  return length;
}

void Test13_test()
{
  Test13_l1.tail = Test13_l2;
}



data List
{
int head;

List tail;
}
 

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;