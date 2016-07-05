void foo(ref int a)
  requires true
  ensures a'=a-1;
{
  a--;
}
