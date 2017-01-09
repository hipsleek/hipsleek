class Exp extends __Exc {
  int val;
}

int loop(int x)
//infer [@post_n]
  requires true
  ensures  res=x+1 & flow __norm;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    /* raise new Exp(2); */
    /* loop(x); */
    return 2;
  } else {
    return x+1;
  }
  dprint;
}

/*
# exc.ss


*/
