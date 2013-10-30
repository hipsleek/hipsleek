int foo(int** q)
/*@
 requires q::int_star_star<r>*r::int_star<a>
 ensures q::int_star_star<null>*r::int_star<a> & res=0;
*/
{
 *q=0;
 return 0;
};

int main()
/*@
 requires true
 ensures true;
*/
{
 int x;
 int* r = &x;
 foo(&r);
 return *r;
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
