#include<stdio.h>
int foo(int** q)
/*@
 requires q::int_star_star<r>*r::int_star<a>
 ensures q::int_star_star<r>*r::int_star<a> & res=0;
*/
{
 q=0;
 return 0;
};

int main()
/*@
 requires true
 ensures res=10;
*/
{
 int x = 10;
 int* r = &x;
 foo(&r);
 int t = *r;
 //printf("*r = %d\n", t);
 return t;
}

/*
short3.c --pcp 
generated without @C 
 int foo$int_star_star(  int_star_star q)

--pip
int foo(int_star_star q)[]

correct answer is in short3.ss
 int foo$int_star_star(  int_star_star q)
 @copy q

--pip
int foo(int_star_star@C q)[]


Maybe this should be traced at --pip
*/
