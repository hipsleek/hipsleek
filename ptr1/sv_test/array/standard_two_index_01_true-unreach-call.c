extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define size 10000
int main()
{
  int a[size];
  int b[size];
  int i = 0;
  int j = 0;
  int tmp;
  while( i < size )
    /*@
      requires  a::arr_seg<j,10000> * b::arr_seg<i,10000> & i=j
      ensures  a::arr_seg<j,10000> * b::arr_seg<i,10000>;
    */
  {
    a[j] = b[i];
        
	
        
        i = i+1;
        j = j+1;
  }

  i = 0;
  j = 0;
  while( i < size )
    /*@
      requires a::arr_seg<i,10000>*b::arr_seg<i,10000> & i=j
      ensures a::arr_seg<i,10000>*b::arr_seg<i,10000>;
    */
  {
	__VERIFIER_assert( a[j] == b[j] );
        i = i+1;
        j = j+1;
  }
  return 0;
}
