/*

  Implement a thread pool using a linked list.
  Forking and storing threads in a ThreadPool (i.e. the thread pool)

  In this program, create a pool of threads, each with a read permission to a cell x
 */

data cell{ int val;}

data item{
  thrd t;
  item next;
}

/* A list of threads, i.e. a thread pool */
threadPool<x,n,M> == self=null & n=0 & M>0
  or self::item<t,p> * p::threadPool<x,n-1,M> * t::thrd<# x::cell(1/M)<_> & true #>
  inv n>=0 & M>0;

//permission splitting. Allow f2=0, if any.
lemma "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0  -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

//permission combine.
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

// Each thread reads the cell x
void thread(cell x, int M)
  requires x::cell(1/M)<_> & M>0
  ensures x::cell(1/M)<_>;
{
  // Perform computation ...
  int tmp = x.val; //read the cell x
  // Perform computation ...
}

item createhelper(cell x, int n, int M)
  requires x::cell(f)<_> & f=n/M & M>=n & n>=0
  ensures res::threadPool<x,n,M> & n>0 or res=null & n=0;
{
  if (n==0){return null;}
  else{
    thrd t = fork(thread,x,M);
    item p = createhelper(x,n-1,M);
    item node = new item(t,p);
    return node;
  }
}

//create a thread pool with n threads
// sharing read accesses to the cell x.
item forkThreads(cell x, int n)
  requires x::cell<_> & n>0
  ensures res::threadPool<x,n,n>;
{
  return createhelper(x,n,n);
}

void joinhelper(item tp, cell x, int n, int M)
  requires tp::threadPool<x,n,M> & M>=n & n>=0
  ensures x::cell(n/M)<_> & n>0
     or true & n=0;
{
  if (tp==null){return;}
  else{
    item node = tp.next;
    joinhelper(node,x,n-1,M);
    thrd t = tp.t;
    join(t);
    destroyItem(tp);
  }
}


// Join all threads in the thread pool
// and get back the full ownership of x.
void joinThreads(item tp, cell x, int n)
  requires tp::threadPool<x,n,n> & n>0
  ensures x::cell<_>;
{
  joinhelper(tp,x,n,n);
}

void destroyCell(cell x)
  requires x::cell<_>
  ensures true;

void destroyItem(item x)
  requires x::item<_,_>
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

  cell x = new cell(1);

  // create a pool consisting of n threads
  item tp = forkThreads(x,n);

  // wait for all threads to finish their execution
  joinThreads(tp,x,n);

  destroyCell(x);
}
