void foo2(ref int i)
 requires i>0
 ensures true;
{
  int r;
  assume 1<=r<=2; //'
  // :assert  assume: (1 <= r#') & (r#' <= 2) FLOW __norm)
  i = i-r;
  dprint;
  bnd(i);
}

void bnd(int i)
 requires i>=0
 ensures true;
