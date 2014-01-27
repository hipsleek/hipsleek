data str {
  int sanitize; // 1-sanitize; 0 :tainted
  int val;
}

int main(int l1, int l2, int h1, int h2)
  requires l1=l2
  ensures res=1;
{
  // Original Program
  l1 = l1 + h1;
  if( h1 != 0 ) { l1 = sub(l1,h1); }
  if( l1 > 0 ) { l1 = sub(l1,1); }

  // Primed Program
  l2 = l2 + h2;
  if( h2 != 0 ) { l2 = sub(l2,h2); }
  if( l2 > 0 ) { l2 = sub(l2,1); }

  if( l1 == l2 ) { return 1; }
  else { return 0; }
}

int sub(int l, int h)
  requires emp
  ensures res=l-h;
{
  return l-h;
}
