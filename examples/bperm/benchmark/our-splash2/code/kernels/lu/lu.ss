/*
  This is a simplified version of the "lu" program
  in SPLASH-2 benchmark.

  This is the "lu" version with non_contiguous_partitions.

  http://www.capsl.udel.edu/splash/
 */


hip_include '../../../../../barrier_static_header.ss'


//lu.C
void lu(barrier start, int n, int bs)
  requires (exists r1: start::barrier(1,2,0)<p> & n=r1*bs & n>0 & bs>0)
  ensures (exists r2: start::barrier(1,2,0)<p1> & n=r2*bs & p1-p=r2*2); //'
{
  // local variable declarations
  //...

  //initializations
  //...

  //LOOP
  int i=0;
  while(i<n)
    requires (exists r1,r2: start::barrier(1,2,0)<p> & n=r1*bs & i=r2*bs & r1>=r2 & bs>0)
    ensures start::barrier(1,2,0)<p1> & 2*(i'-i)=(p1-p)*bs & i<n & i'=n & bs'=bs & start'=start
         or start::barrier(1,2,0)<p1> & p1=p & i>=n & i'=i & bs'=bs & start'=start; //'
  {
    //...

    /* factor diagonal block */
    //...

    waitBarrier(start); //+1

    /* divide column k by diagonal block */
    //...

    /* modify row k by diagonal block */
    //...

    waitBarrier(start); //+1

    /* modify subsequent block columns */
    //...

    //...
    i=i+bs;
  }
}

//lu.C
int TouchA(int bs) requires true ensures true;


//lu.C
void OneSolve(barrier start, int n, int block_size)
  requires (exists r1: start::barrier(1,2,0)<p> & n=r1*block_size & n>0 & block_size>0)
  ensures (exists r2: start::barrier(1,2,0)<p1> & n=r2*block_size & p1-p=r2*2+3); //'
{
  // local variable declarations
  //...

  //initializations
  //...

  /* barrier to ensure all initialization is done */
  waitBarrier(start); //+1

  /* to remove cold-start misses, all processors begin by touching a[] */
  TouchA(block_size);

  waitBarrier(start); //+1

  /* POSSIBLE ENHANCEMENT:  Here is where one might reset the
     statistics that one is measuring about the parallel execution */
  //...

  lu(start, n, block_size);

  //...

  waitBarrier(start); //+1

  //...
}


//lu.C
void SlaveStart(barrier start, int n, int block_size)
  requires (exists r1: start::barrier(1,2,0)<p> & n=r1*block_size & n>0 & block_size>0)
  ensures (exists r2: start::barrier(1,2,0)<p1> & n=r2*block_size & p1-p=r2*2+3); //'
{
  //...

  /* POSSIBLE ENHANCEMENT:  Here is where one might pin processes to
     processors to avoid migration */

  //...
  OneSolve(start, n, block_size);
}


//lu.C
 void CheckResult() requires true ensures true;


//lu.C
void PrintA() requires true ensures true;


//lu.C
void InitA() requires true ensures true;


int random() requires true ensures true;


//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}


//lu.C
void main()
  requires true
  ensures true;
{
  // declare local variables
  // ...
  int n; /* The size of the matrix */
  int P; /* Number of processors */
  int block_size; /* Block dimension */
  int doprint = 0;            /* Print out matrix values? */
  int dostats = 0;            /* Print out individual processor statistics? */
  int test_result = 0;        /* Test result of factorization? */
  barrier start;

  // read inputs from command lines
  //...
  //get from input, P>0
  P = gets();
  // get from input, assume random, n>0
  n = random();
  // get from input, assume random, blocksize>0
  block_size = random();
  assume(exists r: n'=r*block_size' & n'>0 & block_size'>0);//'
  // get from input, assume random
  doprint = random();
  dostats = random();
  test_result = random();

  // ... printf
  //...

  // ... initlization
  //...
  start = newBarrier(P);
  //...

  InitA();
  if (doprint!=0) {
    //printf("Matrix before decomposition:\n");
    PrintA();
  }

  //
  int id1 = fork(SlaveStart,start,n,block_size);
  int id2 = fork(SlaveStart,start,n,block_size);
  //
  join(id1);
  join(id2);

  destroyBarrier(start);

  if (doprint!=0) {
    //printf("\nMatrix after decomposition:\n");
    PrintA();
  }

  if (dostats!=0) {
    // some statistics
    // ...
    ;
  }

  // finalizing
  //...

  // ... printf

  if (test_result!=0) {
    //printf("                             TESTING RESULTS\n");
    CheckResult();
  }

  //MAIN_END
}
