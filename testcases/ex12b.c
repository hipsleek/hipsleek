//Ex.12 - potential double free

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
   for (x = 10; x > 0; x--)
     /*@
       case {
          x>0 -> requires p::int_star<_>
                 ensures x'=0 
                         & a'=p & p'=p;
          x<=0 -> requires emp
                  ensures x'=x & a'=a & p'=p;
       }
     */
   {
       a = p;
       /* dprint; */
       if (x == 1) {
           free(p);
       }
   }
   return 0;
}
