logical int p1, p2, p3, p4;

void f ()
  requires true
  ensures true;
{
  assume true;
}

void g ()
  requires true
  ensures true;
{
  f();g();
}


void m ()
  requires true
  ensures true;
{
  n(); g();
}

void n ()
//infer[p1, p2, p3, p4]
  requires true
  ensures true;
{
  m(); f();
}

void k()
  requires true
  ensures true;
{
  k();
}
