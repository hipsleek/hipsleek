global int n,k;

void decrease1(int t)
   requires [a] t = a+a & a >= 0
   ensures n' = n-a & k' = k-a & t=a+a;
   requires [a] t = a+a+1 & a >= 0
   ensures n' = n-a-1 & k' = k-a & t=a+a+1;
{
   if (t > 0){
	  
		n--;
	
	  decrease2(t-1);
		assume false;
   }
}

void decrease2(int t)
/* global-mutual-rec.ss
   requires t = a+a & a >= 0
   ensures k' = k-a & n' = n-a & t=a+a;
   requires t = b+b+1 & b >= 0
   ensures k' = k-b-1 & n' = n-b & t=b+b+1;
*/
   requires  [a] t = a+a & a >= 0
   ensures k' = k-a & n' = n-a & t=a+a;
   requires [a] t = a+a+1 & a >= 0
   ensures k' = k-a-1 & n' = n-a & t=a+a+1;
{
   if (t > 0) {
	  k--;
	  decrease1(t-1);
   }
}

void main()
   requires true
   ensures n' = 5 & k' = 5;
{
   n = 10;
   int t=5;
   k = 10;
   decrease1(10);
}
