void PastaA1_main()
  infer [@post_n]
  requires true
  ensures true;
{
  int x;
  while (x > 0) 
    infer [@post_n]
    requires true
    ensures true;
  {
    int y = 0;
    while (y < x) 
      infer [@post_n]
      requires true
      ensures true;
    {
      y++;
    }
    x--;
  }
}

