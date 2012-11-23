

void loop(ref int x, int y)
 requires x>0
  case {
  x<y -> requires Term[y-x] ensures true; //x'>=2 & x'>x;
  x>=y -> requires Term[] ensures true; //x'=x; //'
  }
{
  if (x<y) {
    x = x+x;
    loop(x,y);
    }
}

void main(int x, int y)
  requires Term[]
  ensures true;
{
  if (x>3) loop(x,y);
}
