//Ex.7: return the address of a local variable
#include <stdio.h>
 int* foo()
{
   int p = 1;
   int *q = &p; // this setp is necessary to fool gcc/llvm.
   // but smack will be fooled even without it.
   return q;
}

int main()
{
       int *a = foo(); // pointer a points to local variable;
       printf("%d\n",*a);
       return 0;
}
