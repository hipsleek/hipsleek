

data CyclicalListDuplicate
{
CyclicalListDuplicate next;
}
 void CyclicalListDuplicate_main(String[] args)
{
  CyclicalListDuplicate list = CyclicalListDuplicate_generate(args.length);
  if (list != null) {
    CyclicalListDuplicate_duplicate();
  }
}

CyclicalListDuplicate CyclicalListDuplicate_generate(int length)
{
  CyclicalListDuplicate last;
  CyclicalListDuplicate current;
  last = current = new CyclicalListDuplicate(null);
  
  int i = 0;
  while (i < length - 1) {
    current = new CyclicalListDuplicate(current);
    i++;
  }
  
  last.next = current;
  return current;
}

void CyclicalListDuplicate_duplicate(CyclicalListDuplicate _this)
{
  CyclicalListDuplicate current = this;
  boolean even = true;
  while (current != null) {
    if (even) {
      CyclicalListDuplicate copy = new CyclicalListDuplicate(current.next);
      current.next = copy;
    }
    current = current.next;
    even = !even;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;