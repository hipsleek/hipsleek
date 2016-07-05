//./hip errors/hip/err6.ss -tp redlog
//
int helper (int i, int val, int v)
  requires i >= 0 & ((i-1)*(i-1) < val) & (v=i*i -1)
  ensures ((res-1)*(res-1)) <= val & (res*res > val);
{
  v = v + 2*i +1;
  if (v < val)
    return helper(i+1, val, v);
  else return i;
}

//
int squareroot(int val)
  requires val > 0
  ensures ( (res*res <= val) &
          ((res+1)*(res+1) > val));
{
  //int val = 50;
  int i = 1;
  int v=0;
  int r = 0;
  /*
    while(v < val) {
    v = v + 2*i +1;
    i = i+1;
    }
  */
  r = helper(i, val, v); //res=i;
  // r = r - 1;//res = res -1;
  //  assert( (r*r <= val) &
  //        ((r+1)*(r+1) > val));
  return r;
}
