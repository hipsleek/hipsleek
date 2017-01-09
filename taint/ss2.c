struct cell{int val;};


/*@ pred_prim source<b:bool>; */

struct cell* func(struct cell* c) __attribute__ ((noreturn))
/*@
  requires c::cell<a> * c::source<b>
  ensures  res::cell<a> * res::source<b> * c::cell<a> * c::source<b>; //'
*/;

struct cell* func2(struct cell* c, struct cell* d) __attribute__ ((noreturn))
/*@
  requires c::cell<a> * c::source<b> *  d::cell<a1> * d::source<b1>
  ensures  res::cell<a+a1> * res::source<r> & r=(b|b1) ; //'
*/;

void check(struct cell* c) __attribute__ ((noreturn))
/*@
  requires  c::cell<a> * c::source<b> & !b
  ensures true;
*/;

  void test_taint(struct cell* x, struct cell* y, int R1, int R2) 
/*@
    requires x::cell<a1> * x::source<b1>  * y::cell<a2> * y::source<b2> & !b1 & !b2
    ensures  true;
*/
{
  struct cell *z, *a, *b, *c, *d;
  //cell y = new cell(10);// should add a pred prim in the state
  if(R1) z = x; else z = y;
  /* dprint; */
  a = func(z);
  /* dprint; */
  b = func(y);
  c = func(x);
  if(R2) d = func(a);
  else   d = func2(b,c);
  check(d);
}

/*
1: x   S; y   C2; if(?) then z   x else z   y;
2: a  1 f(z); b  2 g(y); c  3 f(x);
3: if(?) then d  4 m(a) else d  5 h(b; c);
4: check(d)
*/
