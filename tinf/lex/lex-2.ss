int irand ()
  requires Term 
  ensures true;
  
bool brand ()
  requires Term
  ensures true;
  
void loop (int x, int y, int d)
  //infer [@term]
  //infer []
  requires true
  ensures true;
{
  if (x > 0 && y > 0 && d > 0) {
    if (brand ()) {
      x = x - 1;
      d = irand ();
    } else {
      x = irand ();
      y = y - 1;
      d = d - 1;
    }
    loop(x, y, d);
  }
}
