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
      ensures  res::arr_seg<q,size>;
      //      ensures res::int_star<_>;
  }
*/;

/* if any pointer is NULL, the behavior of memcpy is undefined */
void *memcpy(int *dest, int *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  false;
  requires src::arr_seg<_, _>@L & dest=null
  ensures  false;
  requires dest::arr_seg<_, _>@L & src=null
  ensures  false;
  requires dest::arr_seg<_, n1> * src::arr_seg<_, n2>@L  & length>=0 & n1>=length & n2>=length
  ensures  dest::arr_seg<_, n2>; //TODO how to capture that the values in dest are clones of src?
*/;

// char a[sizeof(int*)];
int *a;

int** cast_temp(void **p)
/*@
  requires p::void_star_star<_>
  ensures  p::int_star_star<_> & res=p;
*/;



void foo(void)
/*@ //infer[@classic]
  requires a::arr_seg<_,_>
  ensures  a'::arr_seg<_,_>;
*/
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
}


int main(void)
/*@ //infer[@classic]
  requires a::arr_seg<_,_>
  ensures  a'::arr_seg<_,_>;
*/
{
  foo();
  void *pp; // this p will free
  /*@ dprint; */
  //int *x = &pp;
  /*@ dprint; */
  memcpy(&pp, a, sizeof pp);
  /*@ dprint; */
  free((int *)pp);
}


/*
  Q1. are we planning to converge to actual sizes of the primitive types?
  memcpy(a, &p, sizeof p);
  ===>
  in HIP: memcpy(a_78, p, 1)
  in C:   memcpy(a_78, p, 8)

  Q2. What should be the type of & pointer? 
*/
