int irand ()
  requires Term 
  ensures true;
  
bool brand ()
  requires Term
  ensures true;
  
void loop (int x, int y, int z)
  infer [@term]
  requires true
  ensures true;
{
  if (x > 0 && y > 0 && z > 0) {
    if (brand ()) {
      x = x - 1;
    } else if (brand ()) {
      y = y - 1;
      z = irand ();
    } else {
      x = irand ();
      z = z - 1;
    }
    loop(x, y, z);
  }
}
