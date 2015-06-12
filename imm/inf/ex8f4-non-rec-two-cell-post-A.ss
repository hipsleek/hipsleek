data cell{
 int fst;
}

relation P(ann v).
  relation Q(ann v1,ann v2).

int foo2(int n,cell x, cell y)
  infer [Q]
  requires x::cell<v>@a * y::cell<w>@c & a=@L & c=@A
  ensures  x::cell<v>@b * y::cell<w>@d & Q(b,d);
{
 if (n<0) return x.fst;
 return n;
}

/*



*/
