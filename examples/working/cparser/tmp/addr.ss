data int_star {
  int pdata;
}

global int a;


void foo(int_star x)
  requires x::int_star<n>
  ensures x::int_star<n+1>;
{
  x.pdata = x.pdata + 1;
}

void foo1(int_star x)
  requires x::int_star<n>
  ensures x::int_star<2>;
{
  x.pdata = 2;
}


void main()
  requires true
  ensures a' = 2;
{
  a = 1;
  int_star x = new int_star(0);
  x.pdata = a;
  foo(x);
  a=x.pdata;
}
