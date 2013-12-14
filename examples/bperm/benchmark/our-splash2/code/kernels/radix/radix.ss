/*
  This is a simplified version of the "radix" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/
 */

hip_include '../../../../../barrier_static_header.ss'

//radix.C
void slave_sort(barrier barrier_rank, barrier barrier_key, int max_num_digits)
  requires barrier_rank::barrier(1,2,0)<pr> * barrier_key::barrier(1,2,0)<pk> & barrier_rank!=barrier_key & max_num_digits>0
  ensures  barrier_rank::barrier(1,2,0)<pr1> * barrier_key::barrier(1,2,0)<pk+2> & pr1=pr+4*max_num_digits+1;
{
  // Variable declarations and initializations
  //...

  /* POSSIBLE ENHANCEMENT:  Here is where one might pin processes to
     processors to avoid migration */

  /* Fill the random-number array. */
  //...
  initS(); // the original name is init()
  waitBarrier(barrier_key); //+1

  /* POSSIBLE ENHANCEMENT:  Here is where one might reset the
     statistics that one is measuring about the parallel execution */

  waitBarrier(barrier_key); //+1

  //...

  /* Do 1 iteration per digit.  */
  //...


  // LOOP
  int loopnum=0;
  while(loopnum<max_num_digits)
    requires barrier_rank::barrier(1,2,0)<pr>
    ensures barrier_rank::barrier(1,2,0)<pr1> & pr1-pr=(loopnum'-loopnum)*4 & loopnum<max_num_digits & loopnum'=max_num_digits & barrier_rank'=barrier_rank
         or barrier_rank::barrier(1,2,0)<pr1> & pr1=pr & loopnum>=max_num_digits & loopnum'=loopnum & barrier_rank'=barrier_rank; //'
  {
    //...
    /* generate histograms based on one digit */
    //...

    waitBarrier(barrier_rank); //+1

    //...

    waitBarrier(barrier_rank); //+1

    //...

    waitBarrier(barrier_rank); //+1

    //...

    /* put it in order according to this digit */

    //...

    waitBarrier(barrier_rank); //+1

    loopnum++;
  }/* WHILE */

  waitBarrier(barrier_rank); //+1

  //...
}


//radix.C
void initS() requires true ensures true;


//radix.C
void test_sort() requires true ensures true;


//radix.C
void printout() requires true ensures true;


int random() requires true ensures true;


// assume any value greater than 0
int getMaxKey() requires true ensures res>0;


//assuming input=2
int getNumProcs()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}


//radix.C
// assume any value greater than 0
int get_max_digits(int max_key) requires true ensures res>0;


//radix.C
void main()
  requires true
  ensures true;
{
  // variable declarations
  //...
  barrier barrier_rank, barrier_key;
  int number_of_processors;
  int max_num_digits;
  int max_key;
  int dostats = 0;
  int doprint = 0;
  int test_result = 0;
  //...

  // read input from command lines
  //...
  number_of_processors = getNumProcs();
  max_key = getMaxKey();
  doprint = random();
  test_result = random();
  dostats = random();
  //...

  // initialization
  //...
  barrier_rank = newBarrier(number_of_processors);
  barrier_key = newBarrier(number_of_processors);
  //...

  max_num_digits = get_max_digits(max_key);

  //... prinf inputs

  // ...


  /* Fill the random-number array. */
  int id1,id2;
  id1 = fork(slave_sort,barrier_rank,barrier_key,max_num_digits);
  id2 = fork(slave_sort,barrier_rank,barrier_key,max_num_digits);

  //...
  join(id1);
  join(id2);

  //
  destroyBarrier(barrier_rank);
  destroyBarrier(barrier_key);
  //...

  // ... print results
  //...

  if (dostats!=0) {
    // compute and print out statistics
    //...
    ;
  }

  if (doprint!=0) {
    printout();
  }

  if (test_result!=0) {
    test_sort();
  }

}
