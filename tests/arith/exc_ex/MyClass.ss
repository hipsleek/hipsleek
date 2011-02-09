 class Exception extends __Exc{}
 class RuntimeException extends __Exc{}
 class IllegalArgumentException extends RuntimeException{}
 class IllegalStateException extends RuntimeException{}
 
 int blah(int i)
 requires true ensures res = i+2;
	{
       	l1:{
	    try{
		if (i==0) break l1;
		}
	    catch (Exception e){}
	    finally{ i=i+1; };
		};
	i=i+1;
	return i;
    }

    int m() 
	requires true ensures res = 2;
	{
	IllegalArgumentException e = new IllegalArgumentException(); 
	try { 
	    raise e; 
	} catch (IllegalStateException e0) { 
	    return 0; 
	} catch (RuntimeException e1) { 
	    return 1; 
	} finally { 
	    return 2;
	};
    }
