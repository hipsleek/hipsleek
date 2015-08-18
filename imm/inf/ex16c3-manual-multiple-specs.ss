data cell {
 int fst;
 int snd;
}

sum<s> == self::cell<a,b> & s=a+b
  inv self!=null;

relation P1 (ann a).

void simple_read_write(cell c)
  infer [P1]
  requires c::cell<f,h>@aaa & P1(aaa)
  ensures c::cell<g,h> & (g = f + 1);
{
  dprint;
  int tmp = c.fst + 1;
  dprint;
  c.fst = tmp;
}
