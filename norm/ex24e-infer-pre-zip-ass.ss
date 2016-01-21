
relation P(int x, int y).

int zip(int x,int y)
 infer[P]
 requires P(x,y)
 ensures true;
{
  if (x==0) {
    if (y < 0) assert(false); 
    return y;
  } else {
    int r = zip(x-1,y-1);
    return 1+r;
  }
}
