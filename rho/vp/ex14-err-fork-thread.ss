pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

data cell { int val; }

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

/********************************************/
void foo(ref int n)
  requires @full[n] & n>=0
  ensures @full[n] & n'=n+1;
{
  n = n+1;
}


int foo2(int n)
  requires @value[n] & n>=0
  ensures  res=n+1;
{
  n = n+1;
  return n;
}

int foo3(ref int n)
  requires @lend[n] & n>=0
  ensures  res=n+1;
{
  return n+1;
}

int foo4(ref int n)
  requires @frac(1/2)[n] & n>=0
  ensures  @frac(1/2)[n] & res=n+1;
{
  return n+1;
}

int foo5(ref int n)
/*
  requires @frac(f)[n] & n>=0
  ensures  @frac(f)[n] & res=n+1;
*/
  requires @frac(1/213)[n] & n>=0
  ensures  @frac(1/213)[n] & res=n+1;

{
  return n+1;
}

/*

  frac(1/13) |- @frac{f} --> f=1/26
  frac(1/26) 
