data cell{
 int fst;
}

relation P1(ann v1, int v,int i).
relation P2(ann v1, ann v2,int v,int r, int s,int i).
//relation P3(ann v1, int v,int r, int s).

  int foo(cell c,int i)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a,v,i)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P2(a,b,v,res,w,i)  ;
{
 int x = c.fst;
 if (i!=0 && x>0) {
   return 2+foo(c,i-1);
 } else return 0;
}

/*
# ex8e3.ss

{
 int x = c.fst;
 if (i!=0 && x>0) {
   return 2+foo(c,i-1);
 } else return 0;
}

# Fixcalc need not know @L

!!! PROBLEM with fix-point calculation
ExceptionFailure("Trans_arr.extract_translate_scheme: @L To Be Implemented")Occurred!


*/
