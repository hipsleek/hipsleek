void loop (int x, int y, int z)
  infer [@term]
  requires true
  ensures true;
  /*
  case {
    x < 0 & y < 0 -> requires Term ensures true;
    x >= 0 & y >= 0 -> case {
      z >= 1 -> requires Loop ensures false;
      z <= -1 -> requires Loop ensures false;
      z = 0 -> requires Term[x+y] ensures true;
    }
    x >= 0 & y < 0 -> case {
      z >= 1 -> requires Loop ensures false;
      z = 0 | z = -1 -> requires Term[x] ensures true;
      z < -1 -> requires MayLoop ensures true;
    }
    x < 0 & y >= 0 -> case {
      z <= -1 -> requires Loop ensures false;
      z = 0 | z = 1 -> requires Term[y] ensures true;
      z > 1 -> requires MayLoop ensures true;
    }
  }
  */
{
  if (x >= 0 || y >= 0) {
    x = x + z - 1;
    y = y - z - 1;
    loop(x, y, z);
  }
}
