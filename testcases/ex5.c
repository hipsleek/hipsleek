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


/*@ lemma "VOID-INT" self::void_star<x> -> self::int_star<_>.*/

void *malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::void_star<_>;
  }
*/;

/* if any pointer is NULL, the behavior of memcpy is undefined */
void *memcpy(void *dest, void *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  false;
  requires src::void_star<_>@L & dest=null
  ensures  false;
  requires dest::void_star<_>@L & src=null
  ensures  false;
  requires dest::void_star<_> * src::void_star<x>@L  & length>=0 
  ensures  dest::void_star<x>; 

*/;

//char a[sizeof(int*)];
int *a;

void foo()
/*@ infer [@leak]
  requires a::int_star<_>
  ensures  a'::int_star<v> ;
*/
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
  /*@ dprint;*/
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
  void *q = p;
  /*@ dprint; */
  free(q);
}

