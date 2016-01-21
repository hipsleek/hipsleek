
relation P(int x, int y).

int loop(int x,int y)
 infer[P]
 requires P(x,y)
 ensures false;
{
  if (x==0) {
    //if (y < 0) assert(false); 
    return y;
  } else {
    int r = loop(x+y,y+1);
    return 1+r;
  }
}
