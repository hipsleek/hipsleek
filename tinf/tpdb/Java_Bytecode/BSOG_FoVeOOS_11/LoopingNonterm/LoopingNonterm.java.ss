

data LoopingNonterm
{

}
 void LoopingNonterm_main(String[] a)
{
  int i = 0;
  int j = a.length;
  while (i < j) {
    i += a[i]_length();
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;