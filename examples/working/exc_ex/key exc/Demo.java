int mul(int y, int MAX) 
	requires true case{
			y>0 & y>=MAX-> ensures res=MAX;
			y>0 & y<MAX-> ensures res=y;
			y<=0 -> ensures res = 0;
	}	
	{
	int z=0;
	l:while (y>0)
		requires true case{
			y>0 & z+1>MAX -> ensures z'=z & y'=y & flow brk_l;
			y>0 & z+1<=MAX -> ensures z'=z+y & y'=0;
			y<=0 -> ensures y'=y & z'=z;
		}
	{
	    if (z+1>MAX) break l;
	    z = z+1;
	    y = y-1;
	}
	return z;
    }
