/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  inline criteria.
**/

// vanilla is inlineable 'cos a leaf function with no loops.
void vanilla(void)
{
  int x;
  x = x+x;
  if (x) x--;
  else x++;
}

// vanilla_parent inlineable *after* it's call to vanilla has been inlined.
void vanilla_parent(void)
{
  int x;
  x = x + 42;
  vanilla();
  x = x % 4;
}

// looper is not inlineable: contains a loop.
void looper(void)
{
  int i, x;
  for (i=0; i<10; i++) x=x*10;
}

// looper_parent inlineable, but looper isn't.
void looper_parent(void)
{
  int x ;
  x = x + 22 ;
  looper();
  x = x - 2 ;
}

// frec not inlineable: calls itself.
void frec (int x)
{
  if (x==0) return;
  else frec(x-1);
}


void main()
{
  // inline
  vanilla_parent();
  // no inline
  looper();
  // inline parent
  looper_parent();
  frec(99);

}


