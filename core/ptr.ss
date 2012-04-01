global int* p,q;

data integer{
  int val;
}

void delete(ref integer x)
  requires x::integer<>
  ensures true;

void inc()
  requires p::integer<v>
  ensures p::integer<v+1> & p'=p; //'
{
   (*p) = (*p) + 1;
}

void main()
{ int x,y;
   x= 7;
   p =&x;
   inc(p);
   int* ptr;
   ptr=&x;
   int z = x;
   //int z;
   //z = x;
   assert(z'=8);
}

/* global int x; */

/* void func(int x) */
/* requires true */
/*   ensures true; */
/* { */
/*   int x =1; */
/*   x++; */
/*   if (true) { */
/*     int x = 2; */
/*   }else{ */
/*     int x = 3; */
/*     x= x+1; */
/*     int y; */
/*     y=8; */
/*     { */
/*       int y; */
/*       y = 100; */
/*       int z = 10; */
/*     } */
/*   } */
/* } */


/*
More exampes
(1)
int x,y,z;
int*p = &y




*/
