/*
 * HIP/SLEEK standard library for C program
 * 
 * Created: Oct. 31, 2013.
 */


void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h;
  }
*/;

struct GList {
  int key;
  struct GList* prev;
  struct GList* next;
};


int random()
/*@
  requires true
  ensures true;
*/;
