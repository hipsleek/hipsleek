//Ex.12 - potential double free
/*
Proving precondition in method free$int_star Failed.
  (must) cause: do_unmatched_rhs : p'::int_star<Anon_12>@M(must)

Context of Verification Failure: _0:0_0:0

Last Proving Location: testcases/ex12.c_35:11_35:18

Procedure while_15_3$int~int_star~int_star FAIL.(2)


Exception Failure("Proving precond failed") Occurred!


Error(s) detected when checking procedure while_15_3$int~int_star~int_star
*/

int *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::int_star<_>;
  }
*/;

int main() {
   int x, *a;
   int *p = malloc(sizeof(int));
   for (x = 10; x > 0; x--) {
       a = p;
       if (x == 1) {
           free(p);
       }
   }
   return 0;
}
