UTPre@f fpre(int x, int y).
UTPost@f fpost(int x, int y).

void f (int x, int y)

  infer [@term]
  case {
    x < 0 -> requires fpre(x, y) ensures fpost(x, y); 
    x >= 0 -> case {
      y >= 0 -> requires fpre(x, y) ensures fpost(x, y);
      y < 0 -> requires fpre(x, y) ensures fpost(x, y);
    }
  }

{
  if (x < 0) return;
  else f(x + y, y + 1);
}
