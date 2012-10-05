int test(int x)
requires x>0
  ensures x>0 & res=1 ;
{
 if (x>0) {return 1;}
 else {
   assert x>0;
   assert x<=1;
   if (x>2) 
     {return 2;}
   else 
     {return 3;}
 }
}     
