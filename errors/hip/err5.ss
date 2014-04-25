
int userinput()
 requires true
  ensures true;

int foo (int x)
  requires x > 0
  ensures res > 0;
{
  if (x > 5) return x;
  else if (x<2) {
    //assume false;
    return -1;
  }
  else{
    x = userinput(); //char2int(getc)
    if (x>0) return 0;
    else return 1;
  }
}

int goo (ref int x, ref int y)
  requires x > 0 & y > 0
  ensures  x' < 0 & y'< -2;
{
   x = x + 1;
   y = y - 2;
   return x;
}
//[39;35;31;36;32;33]
int test1(ref int x, ref int y)
  requires x = 1 & y = 6
  ensures  res > 0;//'
{
  if (x>0){
   y = x;
   y = y - 2;
  }
   return y;
}
