void foo1(int a1, int b1)
 requires @zero[a1]*@full[b1]
  ensures @full[b1];

void foo2(ref int a2)
 requires @full[a2]
 ensures @zero[a2];

void foo2a(ref int a2a, int b2a)
 requires @full[a2a]
 ensures @zero[a2a];

// requires @full[a]*@value[b]
// ensures @zero[a];

void foo3(ref int a3)
 requires true
 ensures true;
// requires @full[a]
// ensures @full[a];

void foo4(int a4)
 requires true
 ensures true;
// requires @value[a]
// ensures true;

void foo5(int a5, int b5)
  requires @zero[a5]
  ensures true & a5>0;
  // requires @zero[a]*@value[b]
  // ensures true;

void foo6(int a6, ref int b6)
  requires @zero[a6]
  ensures true;
// requires @zero[a]*@full[b]
// ensures @full[b];

void test()
{
  int a;
  foo2(a);
  int b=a;
}

void test2()
{
  int a;
  foo2(a);
  foo3(a); // should fail
}

