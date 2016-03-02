

void foo(int x)
  requires true ensures true;
//    requires x>10 ensures true & __flow Error;

{
  while(x<10)
  case {
    x>=10 -> ensures x'=x;
    x<10 ->  ensures x'=10;
  }
    {
    x++;
  }
    assert (x=10);
}
