/*
  Example of acquiring two locks in
  a strictly increasing order
 */

foo(lock l1,lock l2)
  requires l1 notin ls, l2 notin ls
  ensures ls’=ls
{
   acquire(l1);
   acquire(l2);
   release(l2);
   release(l1);
}

main()
{ 
   lock l; 
   acquire(l);
   id = fork foo(l1,l2);
   acquire(l1);
   acquire(l2);
   release(l1);
   release(l2);
   join(id);
}
