void foo1(int a, int b)
 requires @zero[a]*@full[b]
  ensures @full[b];

void foo2(ref int a)
 requires @full[a]
 ensures @zero[a];

void foo2a(ref int a, int b)
 requires @full[a]
 ensures @zero[a];

// requires @full[a]*@value[b]
// ensures @zero[a];

void foo3(ref int a)
 requires true
 ensures true;
// requires @full[a]
// ensures @full[a];

void foo4(int a)
 requires true
 ensures true;
// requires @value[a]
// ensures true;

void foo5(int a, int b)
 requires @zero[a]
  ensures true;
// requires @zero[a]*@value[b]
// ensures true;

void foo6(int a, ref int b)
 requires @zero[a]
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

