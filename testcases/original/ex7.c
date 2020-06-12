//Ex.8: a pointer to a variableis only valid when the variable
//      is in scope.
#include<stdio.h>
 void foo(int **a)
{
   int b = 1;
   *a = &b;
}

int main()
{
   int *c;
   foo(&c);
   printf("%d\n",*c);
}
