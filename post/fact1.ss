//relation f_pre(int n).
//relation f_post(int n, int r).

int fact(int x)
  infer [@pre,@post]
  requires true  
  ensures true;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
