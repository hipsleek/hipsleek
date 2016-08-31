extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 100000

int main( ) {
  int a1[N];
  int a2[N];
  int a3[N];
  
  int i; 
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a1::arr_seg<i,100000>*a2::arr_seg<i,100000>
      ensures a1::arr_seg<i,100000>*a2::arr_seg<i,100000>;
    */
  {
    a2[i] = a1[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a2::arr_seg<i,100000>*a3::arr_seg<i,100000>
      ensures a2::arr_seg<i,100000>*a3::arr_seg<i,100000>;
    */
  {
    a3[i] = a2[i];
  }
  
  int x;
  for ( x = 0 ; x < N ; x++ ) 
    /*@
      requires a1::arr_seg<x,100000>*a3::arr_seg<x,100000>
      ensures a1::arr_seg<x,100000>*a3::arr_seg<x,100000>;
    */
  {
    __VERIFIER_assert(  a1[x] == a3[x]  );
  }
  return 0;
}

