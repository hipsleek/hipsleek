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

//permission combine.
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

// Each thread reads the cell x
void thread(cell x, int M)
  requires x::cell(1/M)<_>
  ensures x::cell(1/M)<_>;
{
  // Perform computation ...
  int tmp = x.val; //read the cell x
  // Perform computation ...
}

threadNode createhelper(cell x, int n, int M)
  requires x::cell(f)<_> & f=n/M & M>=n & n>=0
  ensures res::threadPool<x,n,M>;
{
  if (n<1){return null;}
  else{
    thrd t = fork(thread,x,M);
    threadNode p = createhelper(x,n-1,M);
    threadNode node = new threadNode(t,p);
    return node;
  }
}

//create a thread pool with n threads
// sharing read accesses to the cell x.
threadNode createThreads(cell x, int n)
  requires x::cell<_> & n>0
  ensures res::threadPool<x,n,n>;
{
  return createhelper(x,n,n);
}

void joinhelper(threadNode tn, cell x, int n, int M)
 /* case { */
 /*  tn=null -> ensures true; */
 /*  tn!=null -> requires tn::threadPool<x,n,M> & M>=n & n>=0 */
 /*           ensures x::cell(n/M)<_>; */
 /*  } */
  requires tn::threadPool<x,n,M> & M>=n & n>=0
  ensures x::cell(n/M)<_> & n>0
     or true & n=0;
{
  if (tn==null){return;}
  else{
    threadNode node = tn.next;
    joinhelper(node,x,n-1,M);
    thrd t = tn.v;
    join(t);
  }
}


// Join all threads in the thread pool
// and get back the full ownership of x.
void joinThreads(threadNode tn, cell x, int n)
  requires tn::threadPool<x,n,n> & n>0
  ensures x::cell<_>;
{
  joinhelper(tn,x,n,n);
}

void destroyCell(cell x)
  requires x::cell<_>
  ensures true;

//receive certain input
int input()
  requires true 
  ensures res>0;

/*
  This program will receive a value n>0
  and create a thread pool of n threads,
  each thread has read accesses to a shared
  cell x. Afterwards, all threads will be joined
  and terminate
 */
void main()
  requires true
  ensures true;
{
  int n = input();

  cell x = new cell(7);

  // create a pool consisting of n threads
  threadNode tn = createThreads(x,n);

  // wait for all threads to finish their execution
  joinThreads(tn,x,n);

  destroyCell(x);
}
