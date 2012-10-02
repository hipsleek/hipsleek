/*
  example of double acquisition in sequential settings
 */
foo(lock l)
  requires waitlevel<<l.mu
  ensures waitlevel’=waitlevel
{
   acquire(l);
   release(l);
}
main()
{ 
   lock l; 
   acquire(l);
   // holds(l) & waitlevel=l.mu
   foo(l);
   release(l);
}
