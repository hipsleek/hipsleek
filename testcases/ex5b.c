//Ex.5: tricky memory leak
// Attempt to have both malloc and memcpy follow the header of the original C methods.

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
      //      ensures res::int_star<_>;
  }
*/;

/* if any pointer is NULL, the behavior of memcpy is undefined */
void *memcpy(void *dest, void *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  false;
  requires src::arr_seg_int<_, _>@L & dest=null
  ensures  false;
  requires dest::arr_seg_int<_, _>@L & src=null
  ensures  false;
  requires dest::arr_seg_int<_, n1> * src::arr_seg_int<_, n2>@L  & length>=0 & n1>=length & n2>=length
  ensures  dest::arr_seg_int<_, n2>; //TODO how to capture that the values in dest are clones of src?
  requires src::arr_seg_void<_, _>@L & dest=null
  ensures  false;
  requires dest::arr_seg_void<_, _>@L & src=null
  ensures  false;
  requires dest::arr_seg_void<_, n1> * src::arr_seg_void<_, n2>@L  & length>=0 & n1>=length & n2>=length
  ensures  dest::arr_seg_void<_, n2>; //TODO how to capture that the values in dest are clones of src?

*/;

// char a[sizeof(int*)];
int *a;

int** cast_temp(void **p)
/*@
  requires p::void_star_star<_>
  ensures  p::int_star_star<_> & res=p;
*/;



void foo(void)
/*@ infer [@leak]
  requires a::arr_seg_void<_,_>
  ensures  a'::arr_seg_void<_,_>;
*/
{
  int *p ;
  /*@ dprint;*/
  p = (int *)malloc(10); // This p will leak
  /*@ dprint;*/
  memcpy((void *)a, (void *)&p, sizeof p);
  /*@ dprint;*/
}


int main(void)
/*@ //infer[@classic]
  requires a::arr_seg_void<_,_>
  ensures  a'::arr_seg_void<_,_>;
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

  Q2. We should be able to preserve more information for the cast to void* and back.
  e.g.
  int_star __cast_void_pointer_to_int_star__(void_star p)
    case{ p != null -> requires p::void_star<_>
                         ensures  res::int_star<_> & res = p;
         p = null   -> requires true ensures res = null
    }

  =====>

  int_star __cast_void_pointer_to_int_star__(void_star p)
    case{ p != null -> requires p::void_star<q>
                       ensures  res::int_star<q> & res = p;
    p = null   -> requires true ensures res = null;
    }

*/


/**
   void foo(int_star@R a_97)[]
   static EInfer @post @leak[] EBase: [][](emp ; (emp ; (a_97::arr_seg_void{}<Anon_31,Anon_32>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 11,:(emp ; (emp ; (a_97'::arr_seg_void{}<Anon_33,Anon_34>[HeapNode1]))) * ([] & true)( FLOW __norm)}
   dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
   {
   {local: int_star p,int_star tmp,int_star_star addr_p
   int_star p
   int_star tmp
   int_star_star addr_p = new int_star_star(p)
   {dprint
   tmp = (129, ):malloc(10)
   member access addr_p~~>value = tmp
   dprint
   (132, ):memcpy((133, ):__cast_int_star_to_void_star__(a_97), (134, ):__cast_int_star_star_to_void_star__(addr_p), 1)
   dprint}}
   }


   void foo(int_star@R a_97)[]
   static EInfer @post @leak[] EBase: [][](emp ; (emp ; (a_97::arr_seg_void{}<Anon_31,Anon_32>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 11,:(emp ; (emp ; (a_97'::arr_seg_void{}<Anon_33,Anon_34>[HeapNode1]))) * ([] & true)( FLOW __norm)}
   dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
   {
   {local: int_star p,void_star tmp,int_star_star addr_p
   int_star p
   void_star tmp
   int_star_star addr_p = new int_star_star(p)
   {dprint
   tmp = (129, ):malloc(10)
   member access addr_p~~>value = (131, ):__cast_void_pointer_to_int_star__(tmp)
   dprint
   (133, ):memcpy((134, ):__cast_int_star_to_void_star__(a_97), (135, ):__cast_int_star_star_to_void_star__(addr_p), 1)
   dprint}}
   }
 */
