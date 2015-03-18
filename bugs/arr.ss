data ptr {
  int val;
}

void foo(ptr a, ref int r)
  //requires a::ptr<_>
  //ensures a::ptr<_>;
  //requires true ensures true;
{
  if (a.val>0) {
    a.val = a.val-1;
    r++;
    foo(a,r);
  }
}
