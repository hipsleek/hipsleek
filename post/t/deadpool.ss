/*

  Forking and storing threads in a threadPool (i.e. the thread pool)
  Joined threads are dead, and are in deadPool

  In this program, assume a pool of threads where each with a read permission to a cell x

 */

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<c:cell, M:int>
inv c!=null & M>0;

pred_prim THRD2{(+)Q@Split}<c:cell,M:int>
inv c!=null & M>0;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<c,M> * self::dead<> -> %Q;

// Each thread reads the cell x
thrd create_thrd() // with %P
  requires true
  ensures (exists x,M: res::THRD{ x::cell(1/M)<_>@S1 & M>0,
                                  x::cell(1/M)<_>
                                }<x,M>);

void fork_thrd(thrd t,cell x, int M)
  requires t::THRD{%P,%Q}<x,M> * %P
  ensures  t::THRD2{%Q}<x,M>;

void join_thrd(thrd t)
  requires exists x,M: t::THRD2{%Q}<x,M>
  ensures  t::dead<> * %Q;
/**************************************/

data cell{ int val;}

data item{
  thrd t;
  item next;
}

/* A list of live threads, i.e. a thread pool */
threadPool<x,n,M> == self=null & n=0 & M>0
  or self::item<t,p> * p::threadPool<x,n-1,M> * t::THRD2{x::cell(1/M)<_>@S1 & true}<x,M>
  inv n>=0 & M>0;

/* A list of dead threads, i.e. a thread pool */
deadPool<n> == self=null & n=0
  or self::item<t,p> * p::deadPool<n-1> * t::dead<>
  inv n>=0;

//permission splitting. Allow f2=0, if any.
lemma_split "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0 -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

//permission combine.
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

// Each thread reads the cell x
void thread(cell x, int M)
  requires x::cell(1/M)<_>@S1 & M>0
  ensures x::cell(1/M)<_>;
{
  // Perform computation ...
  int tmp = x.val; //read the cell x
  // Perform computation ...
}

item forkHelper(cell x, int n, int M)
  case{//more precise
  n=0 -> requires emp ensures emp & res=null;
  n>0 -> requires x::cell(f)<_> & f=n/M & M>=n
         ensures res::threadPool<x,n,M>;
  }
  /* requires x::cell(f)<_> & f=n/M & M>=n & n>=0 */
  /* ensures res::threadPool<x,n,M> & n>0 or res=null & n=0; */
{
  if (n==0){return null;}
  else{
    thrd t = create_thrd();
    fork_thrd(t,x,M);
    item p = forkHelper(x,n-1,M);
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
  return forkHelper(x,n,n);
}

void joinHelper(item tp, cell x, int n, int M)
  requires tp::threadPool<x,n,M> & M>=n & n>=0
  ensures x::cell(n/M)<_> * tp::deadPool<n> & n>0
     or tp::deadPool<n> & n=0;
{
  if (tp==null){return;}
  else{
    item node = tp.next;
    joinHelper(node,x,n-1,M);
    thrd t = tp.t;
    join_thrd(t);
  }
}


// Join all threads in the thread pool
// and get back the full ownership of x.
void joinThreads(item tp, cell x, int n)
  requires tp::threadPool<x,n,n> & n>0
  ensures x::cell<_> * tp::deadPool<n>;
{
  joinHelper(tp,x,n,n);
}

void destroyCell(cell x)
  requires x::cell<_>
  ensures emp;

void destroyItem(item x)
  requires x::item<_,_>
  ensures emp;

void destroyDeadPool(item tp)
  requires tp::deadPool<n>
  ensures emp;
{
  if (tp ==null){
    return;
  }else{
    destroyDeadPool(tp.next);
    destroyItem(tp);
  }
}

//receive certain input
int input()
  requires emp 
  ensures res>0;

/*
  This program will receive a value n>0
  and create a thread pool of n threads,
  each thread has read accesses to a shared
  cell x. Afterwards, all threads will be joined
  and terminate
 */
void main()
  requires emp
  ensures emp;
{
  int n = input();

  cell x = new cell(1);

  // create a pool consisting of n threads
  item tp = forkThreads(x,n);

  // wait for all threads to finish their execution
  joinThreads(tp,x,n);

  destroyCell(x);

  destroyDeadPool(tp);
}

/*
# deadpool.ss -tp parahip --eps -perm fperm --classic

What is Nested Timer(stop)? timeout?
Why errors below? Is it due to lack or normalizing lemma apply?

Procedure destroyDeadPool$item FAIL.(2)
Procedure forkHelper$cell~int~int FAIL.(2)
Procedure forkThreads$cell~int SUCCESS.
Procedure joinHelper$item~cell~int~int FAIL.(2)

Checking procedure destroyDeadPool$item... Nested Timer(stop)
Nested Timer(stop)
Nested Timer(stop)

!!! WARNING logtime exception:9.4e-05
!!! WARNING logtime exception:0.002291
Procedure destroyDeadPool$item FAIL.(2)

Exception Failure("get_node_var: invalid argument") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure destroyDeadPool$item

Proving precondition in method fork_thrd$thrd~cell~int Failed.
  (must) cause: do_unmatched_rhs : x_2379::cell( perm_28_2378)<_>@S1@ rem br[{1}]

Context of Verification Failure: 1 File "",Line:0,Col:0
Last Proving Location: 1 File "deadpool.ss",Line:86,Col:4

Procedure forkHelper$cell~int~int FAIL.(2)

Exception Failure("Proving precond failed") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure forkHelper$cell~int~int

--- sa_logging

Where is __false detected?

!!!Full processing file "../sl_post/post/deadpool.ss"
Parsing file "../sl_post/post/deadpool.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting Omega...oc

Last Proving Location: 1 File "primitives",Line:60,Col:0

ERROR: at _0:0_0:0 
Message: Can not find flow of __false
 Stop Omega... 0 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("Can not find flow of __false")
Error3(s) detected at main 

 */
