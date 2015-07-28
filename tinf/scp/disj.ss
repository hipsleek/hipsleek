/*
void loop (int x, int y, int a, int b) 
{
  if (x > 0 || y > 0) {
    x = x + a - b - 1;
    y = y + b - a - 1;
    loop(x, y, a, b);
  }
}
*/

void main () {
  int x, y, a, b; // all init as nondet();
  if (a != b) { return; }
  // a == b
  while (x > 0 || y > 0) {
    x = x + a - b - 1;
    y = y + b - a - 1;
  }
}
