int sum2 (int n)
   


   case
  {
    n <= 0 -> requires Term[]    ensures true;
    n >  0 -> requires Term[-n]  ensures true;
  }
  
  
   
 
 
{
  if (n > 0)
    return sum2(n-1)+1;
  else {
  
       
          assert n > 0;
        
    return 1;
  }
}
