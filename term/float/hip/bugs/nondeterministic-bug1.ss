// examples from pp. Proving Termination of Nonlinear Command Sequence (Byron Cook) - p.12

bool nondet()
  requires Term[]
  ensures true;

void loop(float n, float j)
  case {
    n <= 1 | n >= 100 		-> requires Term[] ensures true;
    1 < n < 100  & j < 2  -> requires Term[] ensures true;
    1 < n < 100  & j >=2  -> requires Term[Seq{-n@(-infty,-1), -100}] ensures true;
  }
{
  if ((1 <n) && (n<100) && (j>=2))
  {
    if (nondet())
      loop(n*n, j);
    else
    {
    	float j1 = j+1;
    	float n1 = j1;
      loop(n1, j1);
    }
  }
}
