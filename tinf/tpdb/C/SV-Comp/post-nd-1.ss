void main()
{
  int x;
  while (x > 0) 
    infer [@post_n]
    requires true
    ensures true;
  {
    x = x - 1;
  }
}
