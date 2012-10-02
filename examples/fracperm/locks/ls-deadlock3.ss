/*
  example of deadlocks due to interractions of fork/join
  and acquire/release
 */

foo(lock l)
{
   acquire(l);
   release(l);
}

main()
{ 
   lock l; 
   acquire(l);
   int id = fork(foo,l);
   release(l);
   acquire(l);
   join(id);
   release(l);
}
