
relation post(int n, int r).
  relation postA(int n, int r).

  int fact(int n)
  infer [@term]
  requires true ensures true;
{
  return fact(n-1);
}

  int fact1(int n)
  infer [@term]
  requires true ensures true;
{
  if (n==0) return 0;
  else return fact1(n-1);
}

  int fact2(int n)
  infer [@term]
  requires true ensures true;
{
  if (n>=0) return 0;
  else return fact2(n-1);
}

  int fact3(int n)
  infer [@term]
  requires true ensures true;
{
  if (n>=0) return 0;
  else return fact3(n+1);
}

int fact4(int n)
infer [@term]
  requires true ensures true;
{
  if (n==0) return 0;
  else return fact5(n-1);
}

int fact5(int n)
infer [@term]
  requires true ensures true;
{
  if (n==0) return 0;
  else return fact4(n-1);
}

/* int fact1(int n) */
/* infer [@term] */
/*   requires true ensures true; */
/* { */
/*   if (n==0) return 0; */
/*   else return 1+fact1(n-1); */
/* } */

/*
n=0 & res=0 -> post(n)
n!=0 & res=post(n-1)+1 --> post(n)
n!=0 & pre(n) --> pre(n-1)
*/

/* int fact1(int n) */
/* //infer [postA] */
/* infer [@term] */
/* // requires true ensures /\* postA(n,res); *\/ */
/*  requires true ensures true; */
/* { */
/*   if (n==0) return 0; */
/*   else return 1+fact1(n+1); */
/* } */

/* int fact2(int n) */
/* infer [post] */
/*   requires true ensures post(n,res); */
/* { */
/*   if (n==0) return 0; */
/*   else return 2+fact2(0); */
/* } */

/*
n=0 & res=0 --> post(n,res)
n<=-1 & pos(n-1,res-1) --> post(n,res)
n>=1 & pos(n-1,res-1) --> post(n,res)
*/
