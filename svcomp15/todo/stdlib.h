/*
 * HIP/SLEEK standard library for C program
 * 
 * Created: Oct. 31, 2013.
 */

typedef unsigned int size_t;

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h;
  }
*/;

void* calloc(int size, int ssize) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h;
  }
*/;

void* alloca(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h;
  }
*/;

/**************************/
/*** Pointer Arithmetic ***/
/**************************/
int lt___(int* p, int* q)
/*@
  requires p::int*<vp>@L * q::int*<vq>@L
  ensures emp;
*/

/*
  case {
    p <  q -> ensures p::int*<vp> * q::int*<vq> & res > 0;
    p >= q -> ensures p::int*<vp> * q::int*<vq> & res <= 0; }
  requires p::int*<vp, op> * q::int*<vq, oq>
  case {
    op <  oq -> ensures p::int*<vp, op> * q::int*<vq, oq> & res > 0;
    op >= oq -> ensures p::int*<vp, op> * q::int*<vq, oq> & res <= 0; }
*/

;


int abs (int x)
/*@
  case{
    x <  0 -> requires true ensures res = -x;
    x >= 0 -> requires true ensures res = x;
  }
*/
;
