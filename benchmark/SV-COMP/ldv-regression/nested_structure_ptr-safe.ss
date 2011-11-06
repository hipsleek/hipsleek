data InnerMost {
  int c;
}

data Inner {
  int b;
  InnerMost y;
}

data Toplev {
  int a;
  Inner x;
}

void main ()
  requires true
  ensures true;
{
  Toplev good = new Toplev(1,new Inner(2,new InnerMost(3)));
  good.x.y.c = 4;
  assert good.x.y.c!=4;
  return;
}
