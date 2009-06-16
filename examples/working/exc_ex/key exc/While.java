class Exception extends __Exc{}

void loop2(int i) 
	requires true case 
		{i=3 -> ensures true; 
		 i<=0 -> ensures true;
		 i>0& i!=3 -> ensures false;
		}
	{
	int j; 
	while (i>0) 
	requires true case 
		{i=3 -> ensures true; 
		 i<=0 -> ensures true;
		 i>0&i!=3 -> ensures false;
		};
	{
	    if (i==3) {
		return;
	    }     
	}}
    


int loop22(int i) 
	requires true case {
		i<=0 -> ensures res = i;
		i=1 -> ensures res = i' &i'=2;
		i>=2 & i<=3 -> ensures res =3;
		i>3 -> ensures false;}
	{
		tt: while (i>0) 
			requires true case
				{ i<=0-> ensures i'=i;
				  i=1 -> ensures i'=i+1 & flow brk_tt;
				  i=3 -> ensures i'=i & flow brk_tt;
				  i=2 -> ensures i'= 3 & flow brk_tt;
				  i>3 -> ensures false;
				}
			{
			if (i==3) break tt;
			else if (i==1) {i++; break tt;}
			else  i++;
			}
		return i;
    }

void loop3(int i) 
requires true case {
	i<=0 -> ensures true;
	i>0 -> ensures false;}
{
	l:while (i>0) 
		requires true case{
		i<=0 -> ensures true;
		i=3 -> ensures false & flow cnt_l;
		i>0 & i!=3-> ensures false ;}
		{
		if (i==3) continue l; 
		l5:while (true)
				requires true /*case {
				i=6 -> ensures false & flow cnt_l5;
				i=7 -> ensures false & flow cnt_l5;
				i!=6 & i!=7 -> ensures false;}				*/ ensures false;
		{
		    if (i==6) continue l5;
		    if (i==7) continue l5;
		}
		
	    }
}


void loop4(int i) 
	requires true case {
		i<=0 -> ensures true;
		i=3-> ensures true;
		i=7-> ensures true;
		i>0 & i!=3 & i!=7 -> ensures false;}
{
	l:{while (i>0) 
	requires true case{
		i<=0 -> ensures i'=i;
		i=3 -> ensures i'=i & flow brk_l;
		i=7 -> ensures i'=i & flow brk_l;
		i>0 & i!=3 & i!=7 -> ensures false ;}
	{
		if (i==3) break l;
		l5:while (true) 
		requires true case {
				i=6 -> ensures i'=i & flow brk_l5;
				i=7 -> ensures i'=i & flow brk_l;
				i!=6 & i!=7 -> ensures false;}	
		{
		    if (i==6) break l5;
		    if (i==7) break l;
		}
		
	}
	}
}


int loop(int i)
requires true case{
			i<=0 -> ensures res=i;
			i>=4 -> ensures res=3;
			i>0 & i<=3 -> ensures res=0 ;
		} 
{
	try {
	    while (i>0) 
		requires true case{
			i<=0 -> ensures i'=i;
			i>=4 -> ensures i'=3 & flow Exception;
			i>0 & i<=3 -> ensures i'=0 ;
		}
		{
		if (i==3) {
		    i--; 
		    continue;
		} 
		if (i==4) {
		    i--; 
		    raise new Exception ();
		} 
		i--;
	    }
	} catch (Exception e){};
	return i;
}
