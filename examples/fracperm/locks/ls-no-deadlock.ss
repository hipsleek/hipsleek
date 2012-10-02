/*
  An example of deadlock-free programs but may not be
  not provable by related work
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
   join(id);
}
