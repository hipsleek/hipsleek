/*
  example of deadlocks due to interractions of fork/join
  and acquire/release
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
   int id = fork(foo,l);
   join(id);

   release(l);
}
