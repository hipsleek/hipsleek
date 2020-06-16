//Ex.6: return the address of a local variable

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
      //  printf("%d\n",*a);
       return 0;
}

/*

W:

Is it safe to return stack allocated memory?

*/
