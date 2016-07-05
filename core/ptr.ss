global int* p;

void inc(ref int* p)
  requires p::int_ptr<v>
  ensures p::int_ptr<v+1> & p'=p; //'
{
   (*p) = (*p) + 1;
}

void main()
{ int x,y;
   x= 7;
   p =&x;
   inc(p);
   while(true)
     requires true
     ensures true;
   {
     int z=7;
     int* ptr2 = &z;
     z = z +1;
     //expecting delete(z) after translation
   }
   int z = x;
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
