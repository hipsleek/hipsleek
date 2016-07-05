

data Loop1
{

}
 void Loop1_main(String[] args)
{
  
  int i = 0;
  while (i < args.length) {
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