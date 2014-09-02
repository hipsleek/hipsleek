//UTPre@fact fpre(int x).
//UTPost@fact fpost(int x).

int fact(int x)
  infer [@term]
  //requires fpre(x) 
  //ensures res>=1 & fpost(x);
  
  case {
    x = 0 -> requires Term ensures res>=1;
    x != 0 -> requires true ensures res>=1;
  }
  
{
  if (x==0) return 1;
  else {
    return 1 + fact(x - 1);
  }
}