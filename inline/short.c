int foo(int** q)
/*@
 requires q::int__star__star<r>*r::int__star<a>
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
