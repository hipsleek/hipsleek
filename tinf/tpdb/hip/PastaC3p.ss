

data PastaC3
{

}
 void PastaC3_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  int z = Random_random();
  while (x < y) {
    if (x < z) {
      x++;
    } else {
      z++;
    }
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;
