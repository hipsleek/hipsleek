extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 100000

int main( ) {
  int a1[N];
  int a2[N];
  int a3[N];
  int a4[N];
  int a5[N];
  int a6[N];
  int a7[N];
  int a8[N];
  int a9[N];
  
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
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a3::arr_seg<i,100000>*a4::arr_seg<i,100000>
      ensures a3::arr_seg<i,100000>*a4::arr_seg<i,100000>;
    */
  {
    a4[i] = a3[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a4::arr_seg<i,100000>*a5::arr_seg<i,100000>
      ensures a4::arr_seg<i,100000>*a5::arr_seg<i,100000>;
    */
  {
    a5[i] = a4[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a5::arr_seg<i,100000>*a6::arr_seg<i,100000>
      ensures a5::arr_seg<i,100000>*a6::arr_seg<i,100000>;
    */
  {
    a6[i] = a5[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a6::arr_seg<i,100000>*a7::arr_seg<i,100000>
      ensures a6::arr_seg<i,100000>*a7::arr_seg<i,100000>;
    */
  {
    a7[i] = a6[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a7::arr_seg<i,100000>*a8::arr_seg<i,100000>
      ensures a7::arr_seg<i,100000>*a8::arr_seg<i,100000>;
    */
  {
    a8[i] = a7[i];
  }
  for ( i = 0 ; i < N ; i++ ) 
    /*@
      requires a8::arr_seg<i,100000>*a9::arr_seg<i,100000>
      ensures a8::arr_seg<i,100000>*a9::arr_seg<i,100000>;
    */
  {
    a9[i] = a8[i];
  }
  
  int x;
  for ( x = 0 ; x < N ; x++ ) 
    /*@
      requires a1::arr_seg<x,100000>*a9::arr_seg<x,100000>
      ensures a1::arr_seg<x,100000>*a9::arr_seg<x,100000>;
    */
  {
    __VERIFIER_assert(  a1[x] == a9[x]  );
  }
  return 0;
}

