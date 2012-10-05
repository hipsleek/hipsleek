int test(int x)
requires x>0
  ensures x>0 & res=1 ;
{
 if (x>0) {return 1;}
 else {
   return 2;
 }
}     
