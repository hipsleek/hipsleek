relation P(int a).
relation Q(int a,int r).

int foo(int a_5)
  infer [P,Q] requires P(a_5) ensures Q(res,a_5);
{
  if (a_5>10) {
    return a_5;
  } else {
    assume false;
    return -1;
  }
}
