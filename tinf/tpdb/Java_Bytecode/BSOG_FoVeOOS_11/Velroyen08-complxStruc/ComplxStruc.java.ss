

data ComplxStruc
{

}
 void ComplxStruc_loop(int i)
{
  int j = i;
  while (i > 0) {
    if (i >= j) {
      i--;
      if (j < 5) {
        j++;
        if (i - j > 2) {
          i++;
        } else {
          j++;
        }
      } else {
        j--;
      }
    } else {
      if (i > 0 && j < 0) {
        i--;
        if (j < -1) {
          j++;
        } else {
          i++;
        }
      } else {
        i++;
        if (j * 2 > i) {
          j--;
        } else {
          j++;
        }
      }
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  ComplxStruc_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;