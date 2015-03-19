UTPre@f fpre(int x, int y, int z).
UTPost@f fpost(int x, int y, int z).

void f(int x, int y, int z)
  infer [@term]
  requires fpre(x, y, z)
  ensures fpost(x, y, z);
{
  if (x < 0) return;
  else f(x + y, y + z, z);
}
