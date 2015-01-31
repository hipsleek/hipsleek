data cell { int val; }

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  int y = 1;
  int z = 2;
  dprint;
  par {x,y@L,z}
  {
     case {x,y@L} x'::cell<_> ->
       x.val = y + x.val;
  || 
     //case {y@L,z} emp ->
     else ->
       z = z + y;
  }
  dprint;
  assert x'::cell<2> & y'=1 & z'=3;
  assert x'::cell<3> & y'=1 & z'=3;
  assert x'::cell<3> & y'=1 & z'=4;
  assert x'::cell<3> & y'=0 & z'=4;
}
