//

bool nondet()        // nondeterministic function, either return true or false
  requires Term[]
  ensures true;

void loop(float n)
  case {
    n <= 1 | n >= 100  -> requires Term[] ensures true;
    1 < n < 100        -> requires Term[Seq{-n, (-infty,-1), -100}] ensures true;
  }
{
  if ((1 <n) && (n<100))
  {
    if (nondet())
      loop(n*n);
    else
    {
      loop(n+1);
    }
  }
}
