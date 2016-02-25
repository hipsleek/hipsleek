int test(int i)
  requires i>0
  ensures res=2;
{
  int my_var1 = 3;
  int my_var2;
  my_var2 = my_var1 + 5;
  return my_var2;
}
