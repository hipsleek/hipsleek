/*

  Implement a thread pool using a linked list.
  Forking and storing threads in a ThreadPool (i.e. the thread pool)

  In this program, create a pool of threads, each with a read permission to a cell x
 */

data cell{ int val;}

data threadNode{
  thrd v;
  threadNode next;
}

/* A list of threads, i.e. a thread pool */
threadPool<x,n,M> == self=null & n=0
  or self::threadNode<v,p> * p::threadPool<x,n-1,M> * v::thrd<# x::cell(1/M)<_> & true #>
  inv n>=0;

//permission splitting. Allow f2=0, if any.
lemma "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0  -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

// Each thread reads the cell x
void thread(cell x, int M)
  requires x::cell(1/M)<_>
  ensures x::cell(1/M)<_>;
{
  // Perform computation ...
  int tmp = x.val; //read the cell x
  // Perform computation ...
}

threadNode helper(cell x, int n, int M)
  requires x::cell(f)<_> & f=n/M & M>=n & n>=0
  ensures res::threadPool<x,n,M>;
{
  if (n<1){return null;}
  else{
    thrd t = fork(thread,x,M);
    threadNode p = helper(x,n-1,M);
    threadNode node = new threadNode(t,p);
    return node;
  }
}

//create a thread pool with n threads
// sharing read accesses to the cell x.
threadNode createThreadPool(cell x, int n)
  requires x::cell<_> & n>0
  ensures res::threadPool<x,n,n>;
{
  return helper(x,n,n);
}

