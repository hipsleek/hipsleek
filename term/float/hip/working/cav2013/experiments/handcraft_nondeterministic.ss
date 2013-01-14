bool nondet()        // nondeterministic function, either return true or false
  requires Term[]
  ensures true;

float sqrt(float x)
  requires x >= 0.0 & Term[]
  ensures res = __sqrt(x);

void loop(float n)
{
  while ((1 <n) && (n<100))
    case {
      n <= 1      -> requires Term[] ensures true;
      1 < n < 100 -> requires Term[Seq{-n @ (-infty,-1), n < 100}] ensures true;
      n >= 100    -> requires Term[] ensures true;
    }
  {
    if (nondet())
      n = n * sqrt(n);
    else
      n = n * n + 1;
  }
}

