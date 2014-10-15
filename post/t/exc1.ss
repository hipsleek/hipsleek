class Exp extends __Exc {
  int val;
}

int loop(int x)
  requires true
  ensures res=2 & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
  ensures eres.val=2 & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
{
  if (x>0) {
    raise new Exp(2);
    loop(x);
  } else {
    return x+1;
  }
}

/*
# exc1.ss --post-eres

  requires true
  ensures res=2 & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;

If we add res=eres.val thru --post-eres, the post-condition
should be provable.

*/
