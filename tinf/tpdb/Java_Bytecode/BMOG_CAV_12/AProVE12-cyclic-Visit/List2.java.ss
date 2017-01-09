

data List2
{
List2 next;

int mark;
}
 void List2_visit(List2 c)
{
  int expectedMark = c.mark;
  while (c != null && c.mark == expectedMark) {
    c.mark = expectedMark + 1;
    c = c.next;
  }
}

void List2_main(String[] args)
{
  int length = args.length;
  List2 cur = new List2();
  List2 last = cur;
  while (length-- > 0) {
    List2 n = new List2();
    n.next = cur;
    cur = n;
  }
  last.next = cur;
  List2_visit(cur);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;