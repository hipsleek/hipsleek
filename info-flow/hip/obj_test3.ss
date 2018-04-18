relation SEC(int x) == 0 <= x <= 1.

data int_sec {
  int val;
  int sec;
}
data bool_sec {
  bool val;
  int  sec;
}

int LUB(int x, int y)
  requires true
  ensures  res=max(x,y);

int_sec double_if1(int_sec x)
  requires x::int_sec<vx,sx> & sx<=0 & (vx=0|vx=1) & SEC(sx)
  ensures  res::int_sec<vx,sres> & sres<=0 & SEC(sres);
{
  int_sec y = new int_sec(0,0);
  int_sec z = new int_sec(0,0);
  if(x.val == 0) {
    y.val = 1;
    y.sec = LUB(y.sec,x.sec);
  }
  if(y.val == 0) {
    z.val = 1;
    z.sec = LUB(z.sec,y.sec);
  }
  return z;
}

int_sec double_if2(int_sec x)
  requires x::int_sec<vx,sx> & sx<=0 & (vx=0|vx=1) & SEC(sx)
  ensures  res::int_sec<vx,sres> & sres<=1 & SEC(sres);
{
  int_sec y = new int_sec(0,0);
  int_sec z = new int_sec(0,0);
  if(x.val == 0) {
    y.val = 1;
    y.sec = LUB(y.sec,x.sec);
  }
  if(y.val == 0) {
    z.val = 1;
    z.sec = LUB(z.sec,y.sec);
  }
  return z;
}

int_sec double_if3_fail(int_sec x)
  requires x::int_sec<vx,sx> & sx<=1 & (vx=0|vx=1) & SEC(sx)
  ensures  res::int_sec<vx,sres> & sres<=0 & SEC(sres);
{
  int_sec y = new int_sec(0,0);
  int_sec z = new int_sec(0,0);
  if(x.val == 0) {
    y.val = 1;
    y.sec = LUB(y.sec,x.sec);
  }
  // Need a unification of .sec here
  if(y.val == 0) {
    z.val = 1;
    z.sec = LUB(z.sec,y.sec);
  }
  // Need a unification of .sec here
  return z;
}

int_sec double_if4(int_sec x)
  requires x::int_sec<vx,sx> & sx<=1 & (vx=0|vx=1) & SEC(sx)
  ensures  res::int_sec<vx,sres> & sres<=1 & SEC(sres);
{
  int_sec y = new int_sec(0,0);
  int_sec z = new int_sec(0,0);
  if(x.val == 0) {
    y.val = 1;
    y.sec = LUB(y.sec,x.sec);
  }
  if(y.val == 0) {
    z.val = 1;
    z.sec = LUB(z.sec,y.sec);
  }
  return z;
}

int_sec double_ifS(int_sec x)
  requires x::int_sec<vx,sx> & sx<=1 & (vx=0|vx=1) & SEC(sx)
  ensures  res::int_sec<vx,sres> & sres<=sx & SEC(sres);
{
  int sec_ctx_0 = 0;
  int_sec y = new int_sec(0,sec_ctx_0);
  int_sec z = new int_sec(0,sec_ctx_0);
  if(x.val == 0) {
    int sec_ctx_0_1 = LUB(x.sec, sec_ctx_0);
    y.val = 1;
    y.sec = LUB(y.sec,sec_ctx_0_1);
  }
  if(y.val == 0) {
    int sec_ctx_0_1 = LUB(y.sec, sec_ctx_0);
    z.val = 1;
    z.sec = LUB(z.sec,sec_ctx_0_1);
  }
  return z;
}
