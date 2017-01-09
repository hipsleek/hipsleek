class Exception extends __Exc{}

int test(int x, int y, int z)
  requires x=1 & y=1 & z=0 ensures res = 3;
  {
	/*lll:while (x>0) 
		requires true case{
			x>0 -> case {
				y>=1 -> ensures y'=0 & x'=0 & z'=z+x+x+x+y+2;
				y<=0 ->	ensures x'=0 & y'=y & z'=z+x+x+x;}
			//x=0 -> ensures y'=y & z'=z & x'=x & x=0;
			x<=0 -> ensures y'=y & z'=z & x'=x;}*/
	lll:{
	    z++;
	    try {
		b:while (y>0)
			requires x>0 case {
				y>=1 -> ensures y'=0 & z'=z+y & flow cnt_lll;
				y<=0 -> ensures y'=y & z'=z & x'=x;
				}
		    {
			y--;
			z++;
			if (y==0) continue lll; 
			continue b;
		    }
	    } finally{z++;};
	    x--;
	    z++;
	}	
	//dprint;
	return z;
 }

 
void foo (ref int x, ref int z)
//requires true ensures z'=z+x & x'=0 & x>0 or z'=z & x'=x & x<=0;
requires x<=0 ensures z'=z & x'=x ;
requires x>=0 ensures z'=z+x & x'=0 ;
{
	if (x>0) {
		z++;
		x--;
		foo(x,z);
	}
}
 
int test1(int x)
	requires x=1 ensures res=2;
	{	
	int z=0;
	lll:while (x>0) 
		requires true case {
			x>=0 -> ensures z'=z+x+x & x'=0 ;
			x<0 -> ensures z'=z & x'=x ;}
		{
	    z++;
		z++;
	    x--;
	    continue lll;
	}
	return z;
    }

int test2(int x, int y, int z) 
	requires x=1&y=1&z=0 ensures res= 3;
	{
	l1:/*while (x>0) 
	requires true case {
		x>=1 & y>=0 -> ensures z'=z+y+y+y+x+x+x & x'=0 & y'=0; 
		x>=1 & y<0  -> ensures z'=z+x+x+x & x'=0 & y'=y; 
		x<=0 -> ensures x'=x&z'=z&y'=y;}*/
	{
	    z++;
	    try {
	  	l2:while (y>0)
			requires x>0 case{ y>0 -> case{ x=1 -> ensures y'=y-1 & z'=z+1& flow cnt_l1;
											x!=1 -> ensures y'=0 & z'=z+y;}
								y<=0 -> ensures x'=x&z'=z&y'=y ;}
		    {
				y--;
				try{
					l3:while (x==1)
						requires y>=0 
							case {x=1 ->ensures x'=x&z'=z&y'=y & flow cnt_l1;
								  x!=1 ->ensures x'=x&z'=z&y'=y ;
								  }
					{
					continue l1;
					}
				} catch (Exception e){}
				finally {z++;};
		    }
	    } catch (Exception e){}
	    finally{z++;};
	    x--;
	    z++;
	}	
	return z;
    }
