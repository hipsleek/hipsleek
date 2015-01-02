class Exception extends __Exc{}

int tryBreak(int i)
	requires true 
		case {i=0 -> ensures res = i+2;
			  i!=0 -> ensures res = i+3;}			  
{
    l1:{
	    try{
		if (i==0) break l1;
		i=i+1;
		}
	    catch (Exception e){}
	    finally{ 
		i=i+1;
	    };
	}
	i=i+1;
	return i;
}
