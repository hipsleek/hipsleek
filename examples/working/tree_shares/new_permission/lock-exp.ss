/*
An example of deadlock-free programs
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
inv self!=null
inv_lock true; 

void func(lock l1)
requires l1::LOCK<> 
ensures l1::LOCK<>;
{
 acquire(l1);
        release(l1);
        }

void main()
requires true
ensures true; 
{
 lock l1 = new lock();
      init[LOCK](l1); //initialize l1 with invariant LOCK
      release(l1);
      acquire(l1);
      thrd id = fork(func,l1);
      release(l1);
      join(id);
      }
