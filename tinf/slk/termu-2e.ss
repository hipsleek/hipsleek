UTPre@f fpre(int x, int y).
UTPost@f fpost(int x, int y).

UTPre@g gpre(int x).
UTPost@g gpost(int x).

void f(int x, int y)
  infer [@term]
  requires fpre(x, y)
  ensures fpost(x, y);
{
  if (x < 0) return;
  else g(x);
}

void g(int x)
  infer [@term]
  requires gpre(x)
  ensures gpost(x);
{
  if (x < 0) return;
  else f(x - 1, 0);
}
