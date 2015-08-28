
data cell {
 int fst;
 int snd;
}

int simple_read_only(cell c)
  infer [@imm_pre]
  requires c::cell<f@L,g>
  ensures res = (f + g + 1);
{
  int x = c.fst;
  int y = c.snd;
  x = x + 1;
  return x + y;
}


void simple_read_write(cell c)
  infer [@imm_pre]
  requires c::cell<f@M,_>
  ensures c::cell<g,_> & (g = f + 1);
{
  c.fst = c.fst + 1;
}

