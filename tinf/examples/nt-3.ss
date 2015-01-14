/* An example from Gulwani:PLDI08 */
void loop (int x, int y, int m, int n)
  infer [@term]
  requires true
  ensures true;
{
  if (x >= y) return;
  else 
    loop(x + n, y + m, m, n);
}
