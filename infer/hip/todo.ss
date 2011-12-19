void foo2(ref int i)
//infer [i]
 requires i>1
 ensures true;
{
  int r;
  assume 1<=r'<=2; //'
  //assert  assume: (1 <= r) & (r <= 2) FLOW __norm)
  //assert  assume: (1 <= r') & (r' <= 2) FLOW __norm)
  //r_20 = 0; presence of initialization..
  i = i-r;
  dprint;
  bnd(i);
}

void bnd(int i)
 requires i>=0
 ensures true;

// avoid auto initialization (DONE)
// havoc v thru ref parameters
