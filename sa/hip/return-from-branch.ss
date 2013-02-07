int test(int x)
requires x< 0
  ensures res< 0 ;
requires x=5 //x < -1?
  ensures res<0;	
{
 //return -1;
 if (x>10) 
{assert x>10;
return 10;}
 else if (x<2 && x>0 ){
   if(x < -1)	
   {
	assert x < -2;	
	return -10;}
   else
   {
	assert x> 0;
	return -1;}		
 }
 else
 {	
	assert x <= 10;  
	return -3;
 }
}     
