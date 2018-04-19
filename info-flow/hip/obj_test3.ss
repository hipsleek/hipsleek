int_sec double_if1(int_sec x)
  requires x::int_sec<vx,sx> & sx<=0 & (vx=0|vx=1) & 0 <= sx <= 1
  ensures  res::int_sec<vx,sres> & sres<=0 & 0 <= sres <= 1;
{
  int sctx  = 0;
  int_sec y = new int_sec(0,sctx);
  int_sec z = new int_sec(0,sctx);
  int sec_y = y.sec;
  if(x.val == 0) {
    int sctx_0 = LUB(sctx,x.sec);
    y.val = 1;
    y.sec = LUB(y.sec,sctx_0);
  }
  y.sec = LUB(sec_y,y.sec); // MERGE: modified variables
  int sec_z = z.sec;
  if(y.val == 0) {
    int sctx_0 = LUB(sctx,y.sec);
    z.val = 1;
    z.sec = LUB(z.sec,sctx_0);
  }
  z.sec = LUB(sec_z,z.sec); // MERGE: modified variables
  return z;
}

int_sec double_if2(int_sec x)
  requires x::int_sec<vx,sx> & sx<=0 & (vx=0|vx=1) & 0 <= sx <= 1
  ensures  res::int_sec<vx,sres> & sres<=1 & 0 <= sres <= 1;
{
  int sctx  = 0;
  int_sec y = new int_sec(0,sctx);
  int_sec z = new int_sec(0,sctx);
  int sec_y = y.sec;
  if(x.val == 0) {
    int sctx_0 = LUB(sctx,x.sec);
    y.val = 1;
    y.sec = LUB(y.sec,sctx_0);
  }
  y.sec = LUB(sec_y,y.sec); // MERGE: modified variables
  int sec_z = z.sec;
  if(y.val == 0) {
    int sctx_0 = LUB(sctx,y.sec);
    z.val = 1;
    z.sec = LUB(z.sec,sctx_0);
  }
  z.sec = LUB(sec_z,z.sec); // MERGE: modified variables
  return z;
}

int_sec double_if3_fail(int_sec x)
  requires x::int_sec<vx,sx> & sx<=1 & (vx=0|vx=1) & 0 <= sx <= 1
  ensures  res::int_sec<vx,sres> & sres<=0 & 0 <= sres <= 1;
{
  /* int sctx  = 0; */
  int_sec y = new int_sec(0,0);
  int_sec z = new int_sec(0,0);
  int sec_y = y.sec;
  if(x.val == 0) {
    /* int sctx_0 = LUB(0,x.sec); */
    y.val = 1;
    y.sec = LUB(y.sec,x.sec);
  }
  dprint;
  y.sec = LUB(sec_y,y.sec); // MERGE: modified variables
  dprint;
  int sec_z = z.sec;
  if(y.val == 0) {
    /* int sctx_1 = LUB(0,y.sec); */
    z.val = 1;
    z.sec = LUB(z.sec,y.sec);
  }
  z.sec = LUB(sec_z,z.sec); // MERGE: modified variables
  return z;
}

int_sec double_if4(int_sec x)
  requires x::int_sec<vx,sx> & sx<=1 & (vx=0|vx=1) & 0 <= sx <= 1
  ensures  res::int_sec<vx,sres> & sres<=1 & 0 <= sres <= 1;
{
  int sctx  = 0;
  int_sec y = new int_sec(0,sctx);
  int_sec z = new int_sec(0,sctx);
  int sec_y = y.sec;
  if(x.val == 0) {
    int sctx_0 = LUB(sctx,x.sec);
    y.val = 1;
    y.sec = LUB(y.sec,sctx_0);
  }
  dprint;
  y.sec = LUB(sec_y,y.sec); // MERGE: modified variables
  dprint;
  int sec_z = z.sec;
  if(y.val == 0) {
    int sctx_0 = LUB(sctx,y.sec);
    z.val = 1;
    z.sec = LUB(z.sec,sctx_0);
  }
  z.sec = LUB(sec_z,z.sec); // MERGE: modified variables
  return z;
}

int_sec double_ifS(int_sec x)
  requires x::int_sec<vx,sx> & (vx=0|vx=1) & 0 <= sx <= 1
  ensures  res::int_sec<vx,sres> & sres<=sx & 0 <= sres <= 1;
{
  int sctx  = 0;
  int_sec y = new int_sec(0,sctx);
  int_sec z = new int_sec(0,sctx);
  int sec_y = y.sec;
  if(x.val == 0) {
    int sctx_0 = LUB(sctx,x.sec);
    y.val = 1;
    y.sec = LUB(y.sec,sctx_0);
  }
  y.sec = LUB(sec_y,y.sec); // MERGE: modified variables
  int sec_z = z.sec;
  if(y.val == 0) {
    int sctx_0 = LUB(sctx,y.sec);
    z.val = 1;
    z.sec = LUB(z.sec,sctx_0);
  }
  z.sec = LUB(sec_z,z.sec); // MERGE: modified variables
  return z;
}
