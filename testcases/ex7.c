//Ex.7: a pointer to a variableis only valid when the variable
//      is in scope.
void foo(int **a)
/*@
  requires a::int_star_star<v>
  ensures a::int_star_star<v1> * v1::int_star<1>;
*/
{
   int b = 1;
   *a = &b;
}

int main()
/*@
  requires emp
  ensures res=1;
*/
{
   int *c;
   foo(&c);
   return *c;
   // printf("%d\n",*c);
}
