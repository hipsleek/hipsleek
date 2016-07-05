

data Break
{

}
 void Break_main(String[] args)
{
  int i = 0;
  while (true) {
    if (i > 10)
      break;
    i++;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;