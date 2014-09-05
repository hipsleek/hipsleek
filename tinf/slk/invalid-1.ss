UTPre@f fpre(int x).
UTPost@f fpost(int x).

int f(int x)
  infer [@term]
  case {
    x >= 0 -> requires Term[x] ensures fpost(x);
    x < 0 -> requires fpre(x) ensures fpost(x);
  }

{
  return f(x - 1);
}
