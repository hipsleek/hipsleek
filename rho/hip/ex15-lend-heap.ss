data cell { int val; }

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  int y = 1;
  int z = 2;
  //dprint;
  par {x@L,y,z} x'::cell<_>@L
  {
     case {x@L,y} x'::cell<_>@L ->
       y = y + x.val;
  || 
     case {x@L,z} x'::cell<_>@L ->
       z = z + x.val;
  }
  dprint;
  assert x'::cell<1> & y'=2 & z'=3;
  assert x'::cell<2> & y'=2 & z'=3;
  assert x'::cell<1> & y'=3 & z'=3;
  assert x'::cell<1> & y'=2 & z'=4;
}
