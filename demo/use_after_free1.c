//use after free, scenario 1 - simplest scenario


void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & h & s=size & res!=null;
  }
*/;

//void free(int* p) __attribute__ ((noreturn))
/*
  requires p::int*<_> * p::memLoc<h,s> & h & s > 0
  ensures  emp;
*/

void* cast_int(int* x)  __attribute__ ((noreturn))
/*@
case {
  x != null -> requires  x::memLoc<h2,s2> & h2 
               ensures  res::void*<_> * res::memLoc<h2,s2> & h2;
  x = null -> requires true ensures res = null;
}
 */
;

void use_after_free()
{
  int* p = malloc(2);
  int x2;
  free(p);
  x2 = *p + *p;
}
