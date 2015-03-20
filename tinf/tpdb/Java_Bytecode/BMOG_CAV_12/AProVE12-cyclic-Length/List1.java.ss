

data List1
{
List1 pred;

List1 next;
}
 int List1_length(List1 l)
{
  int r = 1;
  while (null != (l = l.next))
    r++;
  return r;
}

void List1_main(String[] args)
{
  int length = args.length;
  List1 cur = new List1(null);
  List1 first = cur;
  while (length-- > 0) {
    cur = new List1(cur);
  }
  List1_length(first);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;