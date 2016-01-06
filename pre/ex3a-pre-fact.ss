relation R(int i, int j,int k).

int fact(ref int i)
  requires true
  ensures  i'=0;
{    
  if (i==0) return 1;
  else {
    int t=i;
    i=i-1;
    return t*fact(i);
  }
}

