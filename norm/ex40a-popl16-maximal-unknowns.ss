relation P(int l, int r).

int lock(int l)
  requires true
  ensures P(l, res);
  
void main () 
  infer [P]
  requires true
  ensures true;
{
  int l = 0;
  l = lock(l);
  dprint;
  assert l'=1;
}
