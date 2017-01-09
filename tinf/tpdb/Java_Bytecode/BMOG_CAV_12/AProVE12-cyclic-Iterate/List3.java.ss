

data List3
{
List3 next;
}
 void List3_iterate(List3 _this)
{
  List3 current = this_next;
  while (current != this) {
    current = current.next;
  }
}

void List3_main(String[] args)
{
  int length = args.length;
  List3 cur = new List3();
  List3 first = cur;
  while (length-- > 0) {
    cur.next = new List3();
    cur = cur.next;
  }
  cur.next = first;
  List3_iterate();
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;