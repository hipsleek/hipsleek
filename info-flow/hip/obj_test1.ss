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

int_sec _addS(int_sec x, int_sec y)
  requires x::int_sec<vx,sx> * y::int_sec<vy,sy>
  ensures  (exists smax:res::int_sec<vx+vy, sres> & sres<=smax & smax=max(sx,sy));
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add1(int_sec x, int_sec y)
  requires x::int_sec<vx,0> * y::int_sec<vy,0>
  ensures  res::int_sec<vx+vy, sres> & sres<=0;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add2(int_sec x, int_sec y)
  requires x::int_sec<vx,0> * y::int_sec<vy,0>
  ensures  res::int_sec<vx+vy, sres> & sres<=1;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add3_fail(int_sec x, int_sec y)
  requires x::int_sec<vx,0> * y::int_sec<vy,1>
  ensures  res::int_sec<vx+vy, sres> & sres<=0;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add4(int_sec x, int_sec y)
  requires x::int_sec<vx,0> * y::int_sec<vy,1>
  ensures  res::int_sec<vx+vy, sres> & sres<=1;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add5_fail(int_sec x, int_sec y)
  requires x::int_sec<vx,1> * y::int_sec<vy,0>
  ensures  res::int_sec<vx+vy, sres> & sres<=0;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add6(int_sec x, int_sec y)
  requires x::int_sec<vx,1> * y::int_sec<vy,0>
  ensures  res::int_sec<vx+vy, sres> & sres<=1;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add7_fail(int_sec x, int_sec y)
  requires x::int_sec<vx,1> * y::int_sec<vy,1>
  ensures  res::int_sec<vx+vy, sres> & sres<=0;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

int_sec _add8(int_sec x, int_sec y)
  requires x::int_sec<vx,1> * y::int_sec<vy,1>
  ensures  res::int_sec<vx+vy, sres> & sres<=1;
{
  int vres = x.val + y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}
