void loop (int x, int y, int z)
  //infer [@term]
  //requires true
  //ensures true;
  case {
    x < 0 & y < 0 -> requires Term ensures true;
    x >= 0 & y >= 0 -> requires Loop ensures false;
    x >= 0 & y < 0 -> case {
      z >= 0 -> requires Loop ensures false;
      z < 0 -> requires MayLoop ensures true;
    }
    x < 0 & y >= 0 -> case {
      z <= 0 -> requires Loop ensures false;
      z > 0 -> requires MayLoop ensures true;
    }
  }
{
  if (x >= 0 || y >= 0) {
    x = x + z;
    y = y - z;
    loop(x, y, z);
  }
}
