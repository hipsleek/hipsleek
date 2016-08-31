extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 100000

int main ( ) {
  int a [N];
  int i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 43;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 44;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 45;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 46;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 47;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 48;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 49;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) 
    /*@
      requires a::arr_seg<i,100000>
      ensures a::arr_seg<i,100000>;
     */
  {
    a[i] = 50;
    i = i + 1;
  }

  int x;
  for ( x = 0 ; x < N ; x++ ) 
    /*@
      requires a::arr_seg<x,100000>
      ensures a::arr_seg<x,100000>;
     */
  {
    __VERIFIER_assert(  a[x] == 50  );
  }
  return 0;
}
