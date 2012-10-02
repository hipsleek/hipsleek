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
   int id = fork(foo,l);
   acquire(l);
   join(id);
   release(l);
}
