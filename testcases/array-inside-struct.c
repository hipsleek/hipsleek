typedef struct _overflow {
  int a[9];
  double c;
} overflow;

/*@
pred buf<arr, d> == self::_overflow<arr, c> & dom(arr, 0, 8);
*/

overflow* malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> 
      requires true 
      ensures res::buf<a, c>;
  }
*/;

int main() 
{
  overflow* s = malloc(sizeof(overflow));

  int i = 10;
  /*
  HIP manages to detect the error with a modification to update___1d in the prelude, that enforces array access to within its bounds. Without it, the error is undetected.
  Updated function spec:
  
  int[] update___1d(int v, ref int[] a, int i)
    requires dom(a, l, h) & l <= i <= h
    ensures update_array_1d(a,res,v,i);


  Proving precondition in method update___1d$int~int[]~int Failed.
  (may) cause: AndR[ dom(v_int_arr_25_1897',0,8) |-  dom(v_int_arr_25_1897',l_1953,h_1954). LOCS:[7;24;25];  dom(v_int_arr_25_1897',0,8) & i'=10 |-  l_1953<=i'. LOCS:[7;24;25];  dom(v_int_arr_25_1897',0,8) & i'=10 |-  i'<=h_1954. LOCS:[7;24;25] (may-bug).]

  Context of Verification Failure: _0:0_0:0

  Last Proving Location: array-inside-struct.c_46:12_46:13

  Procedure main$ FAIL.(2)


  Exception Failure("Proving precond failed") Occurred!
  */
  s->a[i] = 0; //buffer-overflow 1
  s->a[i+1] = 0; //buffer-overflow 2
  s->c = 2.0;
  free(s);
  return 0;
}
