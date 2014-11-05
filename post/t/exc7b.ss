class Exp extends __Exc {
  int val;
}

class Exp2 extends __Exc {
  bool x;
  int y;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true  & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    //dprint;
    if (x>100) raise new Exp(2222);
    else raise new Exp2(true,333);
    loop(x);
  } 
  //else {return x+1;}
  // dprint;
  return x+1111;
}

/*
# exc7b.ss

It seems that res is being taken from the
first parameter of exception, regardless of type!

[RELDEFN post_1256(Exp#E): ( res=2222 & 101<=x) -->  post_1256(x,res),
RELDEFN post_1256(Exp2#E): ( 1<=x & x<=100 & res) -->  post_1256(x,res)]

This may cause a conflict to type. Maybe our
fix-point should allow the object to escape;
and try to capture it ideally as:

 [RELDEFN post_1256(Exp#E): ( 
  res::Exc<2222> & 101<=x) -->  post_1256(x,res),

 RELDEFN post_1256(Exp2#E): 
 ( 1<=x & x<=100 & res::Exp2<true,333>) -->  post_1256(x,res)]

However, this means a cformula rather than formula.

*/
