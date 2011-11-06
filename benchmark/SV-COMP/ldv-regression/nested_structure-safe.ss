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
  InnerMost im = new InnerMost(3);
  Inner inner = new Inner(2,im);
  Toplev good = new Toplev(1,inner);
  good.x.y.c = 4;
  assert good.x.y.c!=4;
  return;
}
