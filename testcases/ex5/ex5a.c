//Ex.5: tricky memory leak

/**********************/
/*** CAST FUNCTIONS ***/
/**********************/
void* __cast_void_star_star_to_void_star__(void** p)
/*@
  case{
  p != null -> requires p::void_star_star<_> 
               ensures  res::void_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

void* __cast_void_star_to_void_star_star__(void** p)
/*@
  case{
  p != null -> requires p::void_star<_> 
               ensures  res::void_star_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;


int* __cast_void_pointer_to_int_star__(void* p)
/*@
  case{
  p != null -> requires p::arr_seg<_> 
               ensures  res::int_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

void* __cast_int_star_to_void_star__(int* p)
/*@
  case{
  p != null -> requires p::int_star<_> 
               ensures  res::void_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

int* __cast_void_star_star_to_int_star__(void** p)
/*@
  case{
  p != null -> requires p::void_star_star<_> 
               ensures  res::int_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

void* __cast_int_star_star_to_void_star__(int** p)
/*@
  case{
  p != null -> requires p::int_star_star<_> 
               ensures  res::void_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

int* __cast_int_star_star_to_int_star__(int** p)
/*@
  case{
  p != null -> requires p::int_star_star<_> 
               ensures  res::int_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

int* __cast_char_star_to_int_star__(char p[])
/*@
  case{
  p != null -> requires p::char_star<_,_> 
               ensures  res::int_star<_> & res = p;
  p = null  -> ensures res = null;
  }
*/;

/**********************/
/******* LEMMAS *******/
/**********************/
/*@ lemma "VOID-INT" self::void_star<x> -> self::int_star<_>. */

// TODO allow type cast at formula level too (this would help us
//      to preserve more information during casting):
// lemma "VOID-INT" self::void_star<x> -> self::int_star<x:int>.


/***************************/
/*** Annotated C methods ***/
/***************************/
void *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::arr_seg<_,size>;
  }
*/;

/* if any pointer is NULL, the behavior of memcpy is undefined */
void *memcpy(void *dest, void *src, int length)
/*@
  requires dest=null & src = null
  ensures  false;
  requires src::arr_seg<_,_>@L & dest=null
  ensures  false;
  requires dest::arr_seg<_,_>@L & src=null
  ensures  false;
  requires dest::arr_seg<_,_> * src::arr_seg<_,n>@L  & length>=0 
  ensures  dest::arr_seg<_,n>; 
*/;


/**********************************/
/*** Pointer Manipulation Logic ***/
/**********************************/
/*@

  data ch_star{
    int val;
  }

  pred arr_seg<p,n> == self::ch_star<_> & self=p & n=1
                    or self::ch_star<_> * q::arr_seg<p,n-1> & q = self + 1 & n > 1
  inv n>=1.

  pred int_block<p> == arr_seg<p,4>.

  pred arr_seg<p,n> == self::ch_star<_> & self=p & n=1
  or self::ch_star<_> * q::arr_seg<p,n-1> & q = self + 1 & n > 1
  inv n>=1.

*/

/*********************/
/*** ORIGINAL CODE ***/
/*********************/

//char a[sizeof(int*)];
int *a;

/* Correctly indetifies the leak in foo:
   Post condition cannot be derived:
   (must) cause: residue is forbidden.(1)
*/

void foo()
/*@ infer [@leak]
  requires a::arr_seg<_,8>
  ensures  a'::arr_seg<_,_>;
*/
{
  int *p = (int *)malloc(10); // This p will leak
  /*@ dprint; */
  memcpy(a, &p, sizeof p);
}


