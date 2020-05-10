//Ex.7: a pointer to a variableis only valid when the variable
//      is in scope.
struct int_s {
  int value;
};

struct int_s *malloc_int_s (int s)
/*@
  requires emp
  ensures res::int_s<_>;
*/;


void foo(struct int_s **a)
/*@
  requires a::int_s_star<v>
  ensures a::int_s_star<v1> * v1::int_s<1>;
*/
{
  struct int_s *addr_b;
  addr_b = malloc_int_s(3);
  (*addr_b).value = 1;
  *a = addr_b;
}

/*

void foo(int_s_star a)[]
static EBase: [][](emp ; (emp ; (a::int_s_star{}<v>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; ((a::int_s_star{}<v1>[HeapNode1]) * (v1::int_s{}<1>[HeapNode1])))) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: int_s b
int_s b = new int_s()
member access b~~>value = 1
member access a~~>value = b}

struct int_s *addr_b;
addr_b = malloc_int_s()
*addr_b.value = 1
*a = addr_b;



It seems that addr_of is NOT being translated for 
non-primitive (struct) type too.

Nice that free is automatically generated.
Perhaps,we should do the same for malloc, where the monomorphic
calls are automatically created nut pre/post can be supplied
by users.

void free(int_s p)[]
static EBase: [][](emp ; (emp ; (p::int_s{}<Anon_11>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 

void free(int_s_star p)[]
static EBase: [][](emp ; (emp ; (p::int_s_star{}<Anon_12>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 3,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 



*/
