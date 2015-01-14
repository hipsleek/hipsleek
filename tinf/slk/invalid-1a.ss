UTPre@f fpre(int x).
UTPost@f fpost(int x).

int f(int x)
  infer [@term]
  //requires fpre(x) ensures fpost(x);
  
  case {
    x >= 0 -> requires fpre(x) ensures fpost(x);
    x < 0 -> requires fpre(x) ensures fpost(x);
  }
  
{
  return f(x - 1);
}
