int sum2 (int n)
   


   case
  {
    n <= 0 -> requires Term[]    ensures true;
    n >  0 -> requires Term[n]  ensures true;
  }
  
  
   
 
 
{
  int tmp;
  if (n > 0) {
    tmp = sum2(n-1);
    return tmp;
  }  else
    return 1;
}
