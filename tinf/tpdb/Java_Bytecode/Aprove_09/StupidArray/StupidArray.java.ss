

data StupidArray
{

}
 void StupidArray_main(String[] args)
{
  int i = 0;
  while (true) {
    i = args.length + 1;
    args[i] = new String();
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;