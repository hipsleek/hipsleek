int foo(int** q)
/*@
 requires q::int^^<a>
 //ensures q::int^^<a> & res=0;
 ensures q::int__star__star<r>*r::int__star<a> & res=0;
*/
{
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
 return x;
}

