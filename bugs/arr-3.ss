data ptr {
  int val;
  int offset;
}

void foo(ptr a, int i, ptr b, ref int r)
  requires a::ptr<_, o> * b::ptr<_, o + i> // b <=> a[i]
  ensures a::ptr<_, o> * b::ptr<_, o + i>;
{
  if (b.val > 0) {
    b.val = b.val-1;
    r++;
    foo(a, i, b, r);
  }
}
