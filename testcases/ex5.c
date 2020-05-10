//Ex.5: tricky memory leak

int *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::int_star<_>;
  }
*/;

/* if any pointer is NULL, the behavior of memcpy is undefined */
void *memcpy(int *dest, int *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  false;
  requires src::int_star<_>@L & dest=null
  ensures  false;
  requires dest::int_star<_>@L & src=null
  ensures  false;
  requires dest::int_star<_> * src::int_star<x>@L  & length>=0 
  ensures  dest::int_star<x>; 

*/;

// char a[sizeof(int*)];
int *a;

void foo(void)
/*@ infer [@leak]
  requires a::int_star<_>
  ensures  a'::int_star<_>;
*/
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
}


int main(void)
/*@
  requires a::int_star<_>
  ensures  a'::int_star<_>;
*/
{
  foo();
  void *p; // this p will free
  memcpy(&p, a, sizeof p);
  /*@ dprint; */
  free((int *)p);
}

