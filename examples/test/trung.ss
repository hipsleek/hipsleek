void foo_term1b(int x)
    case
    {
      x <= 2 -> requires Term[] ensures true;
      x > 2  -> requires Term[x] ensures true;
    }
{
  if (x > 1)
  {
    foo_term1b(x-1);
  }
}
