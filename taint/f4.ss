int add(int l, int h)
  requires true
  ensures res=l+h;
{
  return l+h;
}

int sub(int l, int h)
  requires true
  ensures res=l-h;
{
  return l-h;
}

/* CHECK NON-INTERFERENCE ONLY HERE */
void main(int l1, int l2, int h1, int h2)
  requires true
  ensures true;
{
  assume (l1=l2); // Agree on Public Input

  // Original
  l1 = add(l1,h1);
  l1 = sub(l1,h1);

  // Primed
  l2 = add(l2,h2);
  l2 = sub(l2,h2);

  must_assert (l1=l2); // Agree on Public Output
}

void main2(int l11, int l12, int l21, int l22, int h1, int h2)
  requires h1=0 & h2=0
  ensures true;
{
  assume (l11=l12 & l21=l22);

  l11 = l11 + l21 - h1;
  l12 = l12 + l22 - h2;

  must_assert (l11=l12 & l21=l22);
}
