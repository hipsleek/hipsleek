int rand()
  requires Term
  ensures true;

void f(int xx) 
/*
  case {
    xx < 0 -> requires Term ensures true;
    xx >= 0 -> requires Loop ensures true;
  }
*/
{
  if (xx < 0) return;
  else {
    xx = __VERIFIER_nondet_int() - xx;
    int yy = rand();
    //infer_assume [xx];
    //assume xx' >= 0;
    f(xx);
  }
}
