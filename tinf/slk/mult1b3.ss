UTPre@f2 fpre(int x, int y).
UTPost@f2 fpost1(int x, int y).
UTPost@f2 fpost2(int x, int y).
UTPost@f2 fpost3(int x, int y).

int f2(int x, int y) 
 infer[@term]
//requires true ensures res=0;
// mult1b.ss (new syntax)
  case {
  x<0 -> requires Term[] ensures res=0 & fpost1(x, y);
  x>=0 -> 
   case {
    y<0 -> requires fpre(x, y) // Term[?] 
           ensures fpost2(x, y);
    y>=0 -> requires fpre(x, y) ensures fpost3(x, y);
   }
}
{ if (x<0) return 0;
  else return f2(x+y,y);
}
