//Ex.5: tricky memory leak

/*@
pred arr_seg<p,n> == self::int_star<_> & self=p & n=1
  or self::int_star<_>*q::arr_seg<p,n-1> & q = self + 1 & n > 1
  inv n>=1.
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

void *memcpy(int *dest, int *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  true;
  requires src::arr_seg<_, _> & dest=null
  ensures  true;
  requires dest::arr_seg<_, _> & src=null
  ensures  true;
  requires dest::arr_seg<_, n1> * src::arr_seg<_, n2>  & length>=0 & n1>=length & n2>=length
  ensures  dest::arr_seg<_, n2> * src::arr_seg<_, n2>;
*/;

// char a[sizeof(int*)];
int *a;

void foo(void)
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
}

int main(void)
{
  a = malloc(sizeof(int*));
  foo();
  // void *p ; // this p will free
  int *p ; // this p will free
  memcpy(&p, a, sizeof p);
  free(p);
}
