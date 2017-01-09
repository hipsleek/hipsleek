data cell { int val; }

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  int y = 1;
  int z = 2;
  dprint;
  par {x@L,y@L,z} x'::cell<_>@L
  {
     case {x@L,y@L} x'::cell<_>@L ->
       int v;
       v = y + x.val;
  || 
     case {x@L,y@L,z} x'::cell<_>@L ->
     //else ->
       z = z + x.val;
  }
  dprint;
  assert x'::cell<1> & y'=2 & z'=4;
}
