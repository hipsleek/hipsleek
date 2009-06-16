class Exception extends __Exc{}

int test() 
  requires true ensures res = 6;
  { int x=1,y=1,z=0;
	lll:while (x>0) 
		requires true case{
			x>0 -> case {
				y=1  -> ensures y'=y-1 & z'=z+3 & flow cnt_lll;
				y>1  -> ensures y'=y-1 & z'=z+4 & x'=x-1;
				y<=0 ->
					ensures 
						z'=z+3 & 
							x'=x-1;
						}
			x<=0 -> ensures true;}
	{
	    z++;
	    try {
		b:while (y>0)
			requires true case {
				y=1  -> ensures y'=y-1 & z'=z+1 & flow cnt_lll;
				y>1  -> ensures y'=y-1 & z'=z+1 & flow cnt_b;
				y<=0 -> ensures true;}
		    {
			y--;
			z++;
			if (y==0) continue lll; 
			continue b;
		    }
	    } catch (Exception e){}
	    finally{z++;};
	    x--;
	    z++;
	}	
	return z;
 }

int test1() 
	requires true ensures z=2;
	{	
	int x=1,y=1,z=0;
	lll:while (x>0) 
		requires true case{x>0 -> ensures z'=z+2& x=x-1 & flow __Cont_top; x<=0 -> ensures true;}
		{
	    z++;

	    x--;
	    z++;
	    continue;
	}
	
	return z;
    }

int test2() 
	requires true ensures res= 6;
	{
	int x=1,y=1,z=0;
	l1:while (x>0) 
	requires true case {
		x>0 -> case{ y>0 -> case{ x=1 -> ensures y'=y-1 & z'=z+3& flow cnt_l1;
								 x!=1 -> ensures y'=y-1 & z'=z+4& x'=x-1;
								 }
					y<=0 -> ensures z'=z+3&x'=x-1;}
		x<=0 -> ensures true;}
	{
	    z++;
	    try {
	  	l2:while (y>0)
			requires true case{ y>0 -> case{ x=1 -> ensures y'=y-1 & z'=z+1& flow cnt_l1;
											x!=1 -> ensures y'=y-1 & z'=z+1;}
								y<=0 -> ensures true ;}
		    {
			y--;
			try{
			    l3:while (x==1)
					requires true 
						case {x=1 ->ensures true & flow cnt_l1;
							  x!=1 ->ensures true ;}
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
