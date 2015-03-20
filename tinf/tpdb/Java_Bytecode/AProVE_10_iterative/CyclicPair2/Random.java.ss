
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



data CyclicPair2
{
CyclicPair2 next;
}
 void CyclicPair2_main(String[] args)
{
  Random_args = args;
  CyclicPair2 one = new CyclicPair2();
  CyclicPair2 two = new CyclicPair2();
  int rand = Random_random();
  if (rand != 0) {
    one.next = two;
    two.next = one;
  } else {
    one.next = two;
  }
  if (rand == 0) {
    CyclicPair2_run();
  }
}

void CyclicPair2_run(CyclicPair2 _this)
{
  CyclicPair2 current = this;
  while (current != null)
    current = current.next;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;