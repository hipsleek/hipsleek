UTPre@f fpre1(int x).
UTPost@f fpost1(int x).

UTPre@f fpre2(int x).
UTPost@f fpost2(int x).

void f(int x)
  infer [@term]
  //requires fpre(x)
  //ensures fpost(x);
  
  case {
    x < 0 -> requires fpre1(x) ensures fpost1(x);
    x >= 0 -> requires fpre2(x) ensures fpost2(x);
  }
  
{
  if (x < 0) return;
  else f(x - 1);
}
