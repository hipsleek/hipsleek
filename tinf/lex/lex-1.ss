int irand ()
  requires Term 
  ensures true;
  
bool brand ()
  requires Term
  ensures true;
  
void loop (int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x > 0 && y > 0) {
    if (brand ()) {
      x = x - 1;
    } else {
      x = irand ();
      y = y - 1;
    }
    loop(x, y);
  }
}
