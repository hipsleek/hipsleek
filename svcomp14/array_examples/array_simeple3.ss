##OPTION -- -dre translate

void foo2(ref int[] a)
  requires true
ensures true;
{ 
  a[5] = 1;
  return;
}
