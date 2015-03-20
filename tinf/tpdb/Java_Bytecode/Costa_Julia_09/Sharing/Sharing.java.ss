

data Sharing
{
Sharing next;
}
 void Sharing_iter(Sharing _this, Sharing other)
{
  Sharing cursor = this;
  while (cursor != null) {
    other.next = new Sharing(null);
    other = other.next;
    cursor = cursor.next;
  }
}

void Sharing_main(String[] args)
{
  Sharing sh1 = new Sharing(new Sharing(new Sharing(null)));
  Sharing sh2 = new Sharing(new Sharing(null));
  sh2.next.next = sh2;
  Sharing_iter(sh2);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;