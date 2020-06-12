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

/*
{local: int b
int b
member access b~~>value = 1
member access a~~>value = b}
}

should be:
int_star addr_b;
addr_b = new int_star();
member access addr_b~~>value = 1
member access a~~>value = b}
free(addr_b)


*/
