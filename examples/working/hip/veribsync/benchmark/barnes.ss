/*
  This is a simplified version of the "barnes" program
  in SPLASH-2 benchmark.
  http://www.capsl.udel.edu/splash/
 */

hip_include 'barrier_static_header.ss'

void initparam()
  requires true
  ensures true;
{
  //processing
  //...
  ;
}

/*
 * ANLINIT : initialize ANL macros
 */
void ANLinit(ref barrier b,int NPROC)
  requires NPROC>0
  ensures b'::barrier(NPROC,NPROC,0)<0>;//'
{
  //...
  b = newBarrier(NPROC);
  //...
}

/*
 * STARTRUN: startup hierarchical N-body code.
 */
void startrun(ref barrier b, int NPROC)
  requires NPROC>0
  ensures b'::barrier(NPROC,NPROC,0)<0>;//'
{
  ANLinit(b,NPROC);
}

/*
 * INITOUTPUT: initialize output routines.
 */
void initoutput()
  requires true
  ensures true;
{
  //processing
  //...
  ;
}

/*
 * DIAGNOSTICS: compute set of dynamical diagnostics.
 * code_io.C
 */
void diagnostics()
  requires true
  ensures true;
{
  //processing
  //...
  ;
}

/*
 * OUTPUT: compute diagnostics and output data.
 * code_io.C
 */
void output(barrier b)
  requires  b::barrier(1,2,0)<p>
  ensures b::barrier(1,2,0)<p+1>;
{
  //...
  diagnostics();
  //...
  waitBarrier(b);
  //...
}

/*
 * TAB_INIT : allocate body and cell data space
 */
void tab_init()
  requires true
  ensures true;
{
  //processing
  //...
  ;
}

/*
 * FIND_MY_INITIAL_BODIES: puts into mybodytab the initial list of bodies
 * assigned to the processor.
 */
void find_my_initial_bodies(barrier b)
  requires  b::barrier(1,2,0)<p>
  ensures b::barrier(1,2,0)<p+1>;
{
  //...
  waitBarrier(b);
  //...
}


/*
 * HACKCOFM: descend tree finding center-of-mass coordinates.
 */
void hackcofm()
  requires true
  ensures true;
{
  //processing
  //...
  ;
}

/*
 * MAKETREE: initialize tree structure for hack force calculation.
 */
void maketree(barrier b)
  requires  b::barrier(1,2,0)<p>
  ensures b::barrier(1,2,0)<p+2>;
{
  //processing
  //...
  waitBarrier(b);
  hackcofm();
  waitBarrier(b);
}

/*
 * HOUSEKEEP: reinitialize the different variables (in particular global
 * variables) between each time step.
 */
void Housekeep()
  requires true
  ensures true;
{
  //do house keeping
  //...
  ;
}

void find_my_bodies()
  requires true
  ensures true;
{
  //...
  ;
}

void ComputeForces()
  requires true
  ensures true;
{
  //...
  ;
}

/*
 * STEPSYSTEM: advance N-body system one time-step.
 */
void stepsystem(barrier b)
  requires  b::barrier(1,2,0)<p>
  ensures b::barrier(1,2,0)<p+4>;
{
  //...
  waitBarrier(b);
  //...
  maketree(b);
  //...
  Housekeep();
  //...
  find_my_bodies();
  //...
  ComputeForces();
  //...
  waitBarrier(b);
  //...
}

/*
 * SLAVESTART: main task for each processor
 */
void SlaveStart(barrier b,int tnow, int dtime, int tstop)
  requires (exists r1: b::barrier(1,2,0)<p> & (tstop+10000*dtime-tnow)=r1*dtime & tstop+10000*dtime>tnow & dtime>0)
  ensures (exists r2: b::barrier(1,2,0)<p1> & (tstop+10000*dtime-tnow)=r2*dtime & p1=p+1+r2*4);
{
  //initialize data
  //...

  find_my_initial_bodies(b);//+1

  //...
  // convert the real number loop into correspondent integer loop
  /* while (Local[ProcessId].tnow < tstop + 0.1 * dtime) { */
  /*   stepsystem(b); */
  /* } */
  int n = tstop+10000*dtime;
  while(tnow<n)
    requires (exists r1,r2: b::barrier(1,2,0)<p> & n=r1*dtime & tnow=r2*dtime & r1>=r2 & dtime>0)
    ensures b::barrier(1,2,0)<p1> & tnow<n & tnow'=n & dtime'=dtime & 4*(tnow'-tnow)=(p1-p)*dtime & n'=n & b'=b
         or  b::barrier(1,2,0)<p1> & tnow>=n & tnow'=tnow & p1=p & dtime'=dtime & n'=n & b'=b; //'
   {
      stepsystem(b); //+4
      tnow = tnow + dtime;
   }
  //
}

//read from command line input, assume arbitary
int inputTnow() requires true ensures true;


//read from command line input, assume arbitary
int inputTstop() requires true ensures true;


//read from command line input, assume arbitary
int inputDtime() requires true ensures true;


void main()
  requires true
  ensures true;
{
  barrier b;
  int NPROC=2;
  /* tnow = 0.0; */
  /* tstop (double) : The time to stop integration. */
  /* Default is 0.075. */
  /* dtime (double) : The integration time-step. */
  /* Default is 0.025. */
  /* 0.1 * dtime = 0.0025*/
  /* Note: 
     tnow<(tstop + 0.1 * dtime) is the termination condition
     of the while loop in SlaveStart.
     In order to capture the correctness, we faithfully
     convert real-number operations to integer operations.
     Because, 0.1 * dtime = 0.0025, therefore
     We scale up dtime and tstop by 10000 to become integers.
     and assume that tstop + 0.1 * dtime is also an integer.
  */
  int tnow = inputTnow();
  int tstop = inputTstop();
  int dtime = inputDtime();
  //assumption to ensure that they are integers
  assume(exists r1: tstop'+10000*dtime'-tnow'=r1*dtime' & tstop'+10000*dtime'>tnow' & dtime'>0);

  initparam();
  startrun(b,NPROC);//create barrier with NPROC parties
  initoutput();
  tab_init();
  //
  int id1 = fork(SlaveStart,b,tnow,dtime,tstop);
  int id2 = fork(SlaveStart,b,tnow,dtime,tstop);
  //
  join(id1);
  join(id2);
  destroyBarrier(b);
}
