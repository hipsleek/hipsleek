//#include<stdio.h>

#define MAX(A, B) ((A) > (B) ? (A) : (B))
#define N 100



int main(int a, int b)
/*@
  requires true
  ensures res=100;
*/ 
{


  
  int i = N;
  return MAX(i,3);
}
