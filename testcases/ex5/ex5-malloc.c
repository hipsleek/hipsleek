/* Attempt to make malloc return void*, just like in C. */


/*@
pred arr_seg_int<p,n> == self::int_star<_> & self=p & n=1
  or self::int_star<_>*q::arr_seg_int<p,n-1> & q = self + 1 & n > 1
  inv n>=1.

pred arr_seg_void<p,n> == self::void_star<_> & self=p & n=1
  or self::void_star<_>*q::arr_seg_void<p,n-1> & q = self + 1 & n > 1
  inv n>=1.

*/

void *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures  res::arr_seg_void<q,size>;
  }
*/;


int* cast_temp(void *v)
/*@
  requires v::arr_seg_void<q,s>
  ensures  res::arr_seg_int<q,s> & res=v; 
 */;


void foo(void)
{
  int *p ;
  /*@ dprint;*/
  void *v = malloc(10);
  /*@ dprint;*/
  p = cast_temp(v); // This p will leak
  /*@ dprint;*/
}

