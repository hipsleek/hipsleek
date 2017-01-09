
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



data CyclicPair
{
CyclicPair next;
}
 void CyclicPair_main(String[] args)
{
  Random_args = args;
  CyclicPair one = new CyclicPair();
  CyclicPair two = new CyclicPair();
  int i = Random_random();
  if (i == 0) {
    two.next = two;
  } else {
    one.next = one;
  }
  while (two.next == two && one.next == one) {
    one.next = two;
    two.next = one;
    one.next = two.next;
    two.next = two;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;