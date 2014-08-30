UTPre@f fpre(int x).
UTPost@f fpost(int x).

void f(int x)
  infer [@term]
  //requires fpre(x)
  //ensures fpost(x);
  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
  
{
  if (x < 0) return;
  else f(x - 1);
}
