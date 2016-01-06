relation R(int i, int j,int k).

int fact(ref int i)
 case {
   i<0 -> ensures false;
   i>=0 ->  ensures  res>=1 & i'=0;
  }
{    
  if (i==0) return 1;
  else {
    int t=i;
    i=i-1;
    return t*fact(i);
  }
}

