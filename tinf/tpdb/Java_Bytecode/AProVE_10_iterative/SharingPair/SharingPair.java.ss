

data SharingPair
{
SharingPair next;
}
 void SharingPair_main(String[] args)
{
  Random_args = args;
  SharingPair one = new SharingPair();
  SharingPair two = new SharingPair();
  SharingPair cur;
  int i = Random_random();
  if (i == 0) {
    one.next = two;
    cur = one;
  } else {
    two.next = one;
    cur = two;
  }
  while (true) {
    if (i == 0) {
      one.next = new SharingPair();
      cur = cur.next;
    } else {
      two.next = new SharingPair();
      cur = cur.next;
    }
  }
}


global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;