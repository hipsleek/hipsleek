relation input_match(int a, int b, int c, int d) == true.

int firstarg(int a, int b)
  requires [c,d] input_match(a,b,c,d) & a>=c & b>=d & a >= 0 & b >= 0
  ensures res = a & res >= c;
{
  return a;
}

int main()
  requires true
  ensures res = 3;
{
  int a = 5;
  int b = 3;
  int d = 3;
  assume input_match(a',b',0,0);
  int c = firstarg(a,b);
  assume input_match(b',a',0,0);
  return firstarg(b,a);
}
