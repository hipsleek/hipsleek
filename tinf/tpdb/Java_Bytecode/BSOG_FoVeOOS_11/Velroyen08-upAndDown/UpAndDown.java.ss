

data UpAndDown
{

}
 void UpAndDown_upAndDown(int i)
{
  boolean up = false;
  while (0 <= i && i <= 10) {
    if (i == 10) {
      up = false;
    }
    if (i == 0) {
      up = true;
    }
    if (up) {
      i++;
    } else {
      i--;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  UpAndDown_upAndDown(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;