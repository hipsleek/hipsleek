int test_fun(int x, int y, int z)
	requires x>=z & y>0 
	ensures res=2;
{
        while (x >= z) {
          if(y <= 0) {
                // replace assume
                return 1;
                }
          return 2;
        }
    return z;
}
