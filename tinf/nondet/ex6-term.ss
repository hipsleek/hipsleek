void loop (int x, int y, int z) {
  if (x - y > 0) {
      loop(-x + y, z, z + 1);
  }
}

void rloop (ref int x, ref int y, ref int z) {
  if (x - y > 0) {
      x = -x + y;
      y = z;
      z = z + 1;
      rloop(x, y, z);
  }
}
