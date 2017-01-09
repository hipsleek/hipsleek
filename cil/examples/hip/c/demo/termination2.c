int sum2 (int n)
/*@ 


   case
  {
    n <= 0 -> requires Term[]    ensures true;
    n >  0 -> requires Term[n]  ensures true;
  }
  
  
 */
 
 
{
  int tmp, aaaaa, bbb;
  aaaaa = 2;
  bbb = 3;
  if (n > 0) {
    tmp = sum2(n-1);
    return tmp;
  }else
    return 1;
}
