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
  p != null -> requires p::void_star<_>
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
int *memcpy(int *dest, int *src, int length)
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
  requires a::int_star<_>
  ensures  a'::int_star<v>;
*/
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
  /*@ dprint; */
  // p is now a void *, explicitly cast it back to int * to comply with ensures  a'::int_star<v>;
  p = (int *)&p;
}


int main(void)
/*@
  requires a::int_star<_>
  ensures  a'::int_star<_>;
*/
{
  foo();
  void *p; // this p will free
  /*@ dprint; */
  memcpy(&p, a, sizeof p);
  /*@ dprint; */
  free(p);
}
