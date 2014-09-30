/* zip - numeric */

relation P(int a,int b).

void pos(int a)
  requires a>0
  ensures true;

int zip(int x, int y)
  infer [P]
  requires P(x,y)
  ensures  true;
{
  if (x==0) return 0;
  else {
    pos(y);
    //dprint;
    pos(x);
    pos(y);
    //dprint;
    return 1;  
  }
}










