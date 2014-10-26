void loop (int x, int y, int z, int t)
  infer [@term]
  requires true
  ensures true;
  /*
  case {
    x >= 0 | y >= 0 -> case {
      z >= 1 -> requires true ensures true;
      z <= 0 -> requires true ensures true;
    }
    x < 0 & y < 0 -> requires true ensures true;
  }
  */
{
  if (x >= 0 || y >= 0) {
    x = x + z - t - 1;
    y = y + z - t - 1;
    loop(x, y, z, t);
  }
}
