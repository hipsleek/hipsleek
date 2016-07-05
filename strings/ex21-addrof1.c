int a;

void foo(int* x)
/*
  requires x::int*<n>
  ensures x::int*<n+1>;
*/
{
  *x = *x+1;
}


void main()
/*
  requires true
  ensures a' = 2;
*/
{
  a = 1;
  foo(&a);
}

/*
# ex21.c

{
  *x = *x+1;
}

This C program using int_star is no longer working due to conversion
to _get_char


void main(int@R a_56)[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp) * ([] & a_56' = 2)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: int_star addr_a
int_star addr_a = new int_star(a_56)
__get_char_(addr_a) = 1
(95, ):foo(addr_a)}
}

*/
