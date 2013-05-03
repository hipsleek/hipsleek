global int y =0;

int foo (int a, int b, int x)
  requires a=0 & b=-2 & x=1
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}
/*
filter_ante inp1 : a=a' & b=b' & x=x_762 & y_15=y_772 & a=0 & b+2=0 & x=1 & x_767=a'+x_762 & 
x'=b'+x_767 & y_15'=a'+y_772 & res=x'
filter_ante inp2 : 0<=res

1.  a=a' & b=b' & x=x_762 & y_15=y_772 & a=0 & b+2=0 & x=1 & x_767=a'+x_762 & 
res=b'+x_767 & y_15'=a'+y_772

 */
relation H(int a, int b, int c).

/*
H(a,b,x)) -->  0<=(x+a+b)
*/
int goo (int a, int b, int x)
  infer [H]
  requires H(a, b, x)
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}
