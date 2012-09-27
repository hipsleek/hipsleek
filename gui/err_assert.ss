int testAssert(int x, int y)
  requires x>0 
  ensures res>=0;
{    
	if (x==1){
	   assert(x>1);			 
           return 0;
	}
    	else
           return 1;
}
