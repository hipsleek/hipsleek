relation P(int l, int r).

int lock(int l)
  requires true
  ensures P(l, res);
  
void main () 
  requires true
  ensures true;
{
  int l = 0;
  while (rand_bool()) 
    infer [P]
    requires true
    ensures true;
  {
    l = lock(l);
    dprint;
    assert l'=1;
  }
}
