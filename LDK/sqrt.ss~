
int foo(int n) 
 requires n>=0
  ensures res=n;
{
int i = 0;
while (i < n) 

 case{
   i<=n -> requires n>=0 ensures i'=n;
   i>n -> ensures i'=i;
 }

  {
    i = i+1;
  }
 return i;
}
