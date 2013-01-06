/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires y>=0 & x>=0 & P(x,y)
  ensures  true;

/*
[RELDEFN P: ( x=v_int_77_513'+1 & y=v_int_77_512'+1 & 0<=v_int_77_513' & 
v_int_77_513'<=v_int_77_512' & P(x,y)) -->  P(v_int_77_513',v_int_77_512')]


*/
{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1;
  }
}










