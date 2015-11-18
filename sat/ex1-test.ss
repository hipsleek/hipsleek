int foo(int x)
  requires true
  ensures res=x+4;
{
  x = x+3;
  return x;
}

/*

Must failure:

  (i)  contra detected
  (ii) SAT(res=3+x)

  (must) cause:  res=3+x |-  res=x+4. LOCS:[1;5;6;3] (must-bug)



*/

bool rand()
  requires true
  ensures res or !res;

int foo2(int x)
  requires true
  ensures res=x+4;
{
  if (rand()) x = x+3;
  else x=x+4;
  return x;
}

