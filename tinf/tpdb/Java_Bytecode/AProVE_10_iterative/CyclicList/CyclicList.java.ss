

data CyclicList
{
CyclicList next;
}
 void CyclicList_main(String[] args)
{
  CyclicList list = CyclicList_create(args.length);
  CyclicList_get(args[0]_length());
}

CyclicList CyclicList_create(int x)
{
  CyclicList last;
  CyclicList current;
  last = current = new CyclicList(null);
  while (--x > 0)
    current = new CyclicList(current);
  return last.next = current;
}

CyclicList CyclicList_get(CyclicList _this, int n)
{
  CyclicList cur = this;
  while (--n > 0) {
    cur = cur.next;
  }
  return cur;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;