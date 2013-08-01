

int foo(int N) 
 requires N>=0
 ensures res=N;
{
 int i = 0;
 loop(i,N);
 return i;
}

void loop(ref int i, int N)
  requires i<=N
  ensures i'=N;
{ 
   if (i<N) {
      i=i+1;
      loop(i,N);
   }
}


