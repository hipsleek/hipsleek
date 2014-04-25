void foo1(ref int i)
 requires i>0
 ensures i'=i-1; //'
{
  i = i-1;
  bnd(i);
}


void foo2(ref int i)
 requires i>1
 ensures i-2<=i'<=i-1; //'
{
  int r;
  //assume 1<=r<=2; 
  ass(r);
  i = i-r;
  //dprint;
  bnd(i);
}


void bnd(int i)
 requires i>=0
 ensures true;

void ass(ref int r)
 requires true
 ensures 1<=r'<=2;
