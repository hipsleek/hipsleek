int foo(int x) 
 infer[@term]
  requires true
  ensures true;
/*
 case {
  x<0 -> ensures res=0;
  x>=0 -> ensures false;
}
*/
{ if (x==0) return 0;
  else 
    { if (x<0) return foo(-x);
       else return foo(-x);
    };
}

