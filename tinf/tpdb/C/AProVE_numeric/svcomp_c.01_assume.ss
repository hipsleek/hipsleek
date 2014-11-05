void loop (int x, int y)
{
  while (x >= 0) {
    y = 1;
    while (x > y) {
      if(y <= 0) {
        break;
      }
      y = 2*y;
    }
    x = x - 1;
  }
}
