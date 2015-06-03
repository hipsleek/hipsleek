data cell{
 int fst;
}

relation P(ann v).
  relation Q(ann v1,ann v2).



int foo1(int n,cell x, cell y)
  infer [Q]
  requires x::cell<v>@a * y::cell<w>@c & Q(a,c)
  ensures  x::cell<v>@b * y::cell<w>@d  ;
{
 if (n<0) return x.fst;
 return n;
}



/*



*/
