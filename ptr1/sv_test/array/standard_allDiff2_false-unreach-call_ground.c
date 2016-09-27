extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 100000

int main( ) {
  int a[10];
  int i;
  int r = 1;
  for ( i = 1 ; i < N && r ; i++ )
    /*@
      requires a::arr_seg<0,100000>
      ensures a::arr_seg<0,100000>;
    */
    {
    int j;
    for ( j = i-1 ; j >= 0 && r ; j--)
      /*@
        requires a::arr_seg<0,j+1> * xx::arrI<_> & xx = a+i & i>=1 & j<i & j>=0
        ensures a::arr_seg<0,j+1> * xx::arrI<_>;
      */
      {
      if ( a[j] ==0 ) {
        r = 1;
      }
    }
  }
  
  /* if ( r ) { */
  /*   int x; */
  /*   int y; */
  /*   for ( x = 0 ; x < N ; x++ ) { */
  /*     for ( y = x+1 ; y < N ; y++ ) { */
  /*       __VERIFIER_assert(  a[x] != a[y]  ); */
  /*     } */
  /*   } */
  /* } */
  return 0;
}
