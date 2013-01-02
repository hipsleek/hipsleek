

int foo(int N) 
 requires N>=0
 ensures res=N;
{
 int i = 0;
 while (true) 
  requires i<=N
  ensures i'=N ;
  {
    if (i>=N) return i; 
    i = i+1;
  }

}


