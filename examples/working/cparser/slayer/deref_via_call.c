/*
  Copyright (c) Microsoft Corporation.  All rights reserved.

  deref_via_call.c : assign into a local, but by passing it's address down a
  chain of function calls.

  This program should be safe: it should never assign *0=0.

  This was a test case to check frontend_slam's local declaration correctness:
  parent functions used to declare their child functions locals.

*/
//#include <slayer.h>

int uninit_g_x ;
int* uninit_g_py ;
int uninit_g_z ;

int a,b,c;

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

void g(int** g_ppi)
/*@
  requires g_ppi::int**<t>@L * t::int*<_>
  ensures t::int*<q> & q != 0;
*/
{
  **g_ppi = &a;
}

void f(int* f_pi)
/*@
  requires f_pi::int*<_>
  ensures f_pi::int*<q> & q != 0;
*/
{
  int** f_ppi;
  f_ppi = &f_pi;
  g(f_ppi);
}

void main ()
{
  int *p = (int*) malloc (sizeof(int));
  *p = &b;
  f(p);
  *p = &c;
  f(p);
  *p = 0;
  f(p);

  // assert *p != 0
  //FAIL_IF( (*p) == 0 );
  //@ assert p'::int^<m> & m!=0;

  return;
}
