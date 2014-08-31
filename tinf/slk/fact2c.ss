UTPre@f fpre(int x).
UTPost@f fpost(int x).

int fact(int x)
  infer [@term]
  case {
    x = 0 -> requires Term[] ensures res>=1 & fpost(x);
    x != 0 -> requires fpre(x) ensures res>=1 & fpost(x);
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}


