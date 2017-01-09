/*
  This is a simplified version of the "fft" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/
 */


hip_include '../../../../../barrier_static_header.ss'


//fft.C
void SlaveStart(barrier start, int test_result)
  requires start::barrier(1,2,0)<p>
  ensures start::barrier(1,2,0)<p+7> & test_result=0
          or start::barrier(1,2,0)<p+12> & test_result!=0;
{
  //local variable declarations and initialization
  int MyFirst;
  int MyLast;
  //...

  /* POSSIBLE ENHANCEMENT:  Here is where one might pin processes to
   processors to avoid migration */

  waitBarrier(start); //+1

  //...

  // compute MyFirst and MyLast, assume unknow outcome
  MyFirst = random();
  MyLast = random();

  TouchArray();

  waitBarrier(start); //+1

/* POSSIBLE ENHANCEMENT:  Here is where one might reset the
   statistics that one is measuring about the parallel execution */

  /* perform forward FFT */
  FFT1D(start, 1, MyFirst, MyLast);//+5

  /* perform backward FFT */
  if (test_result!=0) {
    FFT1D(start, -1, MyFirst, MyLast);//+5
  }

  //...
}


//fft.C
void FFT1D(barrier start,int direction, int MyFirst, int MyLast)
  requires start::barrier(1,2,0)<p>
  ensures start::barrier(1,2,0)<p+5>;
{
  // local variables
  //...

  waitBarrier(start); //+1

  /* transpose from x into scratch */
  Transpose();
  //...

  /* do n1 1D FFTs on columns */
  int j = MyFirst;
  while (j<MyLast)
    requires true
    ensures true;
  {
    FFT1DOnce(direction);
    TwiddleOneCol(direction);
    j++;
  }

  waitBarrier(start); //+1

  //...

  /* transpose */
  Transpose();
  //...

  /* do n1 1D FFTs on columns again */
  j = MyFirst;
  while (j<MyLast)
    requires true
    ensures true;
  {
    FFT1DOnce(direction);
    if (direction == -1){
      Scale();
    }
    j++;
  }

  waitBarrier(start); //+1

  /* transpose back */
  Transpose();
  //...

  waitBarrier(start); //+1

  /* copy columns from scratch to x */
  //...

  waitBarrier(start); //+1
}

//fft.C
void Scale() requires true ensures true;


//fft.C
void TwiddleOneCol(int direction) requires true ensures true;


//fft.C
void FFT1DOnce(int direction)
  requires true ensures true;
{
  //local variables and initialization
  //...

  Reverse();

  //do computation
  //...
}

//fft.C
void Reverse() requires true ensures true;


//fft.C
void Transpose() requires true ensures true;


//fft.C
void TouchArray() requires true ensures true;


//fft.C
void PrintArray() requires true ensures true;


//fft.C
void CheckSum() requires true ensures true;


//fft.C
void InitU2() requires true ensures true;


//fft.C
void InitU() requires true ensures true;


//fft.C
void InitX() requires true ensures true;


// assume unknown outcome
int random() requires true ensures true;


// get a random input from command line
int getInput() requires true ensures true;


//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}


//fft.C
void main()
  requires true
  ensures true;
{
  // variables declarations
  //...
  /* P = number of processors; Must be a power of 2.  */
  int P;
  barrier start;
  int test_result = 0;
  int doprint = 0;
  // read command line input
  //...
  P = gets();
  /* test_result = getInput(); */
  /* doprint = getInput(); */
  //initialization
  //...

  //...printf

  start = newBarrier(P);
  //...
  InitX(); /* place random values in x */

  if (test_result!=0) {
    CheckSum();
  }
  if (doprint!=0) {
    //some printing
    PrintArray();
  }

  //...

  InitU();               /* initialize u arrays*/
  InitU2();

  /* fire off P processes */
  int id1 = fork(SlaveStart,start,test_result);
  int id2 = fork(SlaveStart,start,test_result);
  //
  join(id1);
  join(id2);

  if (doprint!=0) {
    if (test_result!=0) {
      //printf("Data values after inverse FFT:\n");
      ;
    } else {
      //printf("Data values after FFT:\n");
      ;
    }
    PrintArray();
  }

  //finalizing...
  destroyBarrier(start);
  //printf ...

  //MAIN_END
}
