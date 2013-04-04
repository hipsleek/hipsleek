/*
  This is a simplified version of code.C
 */

//permission rules for static barrier
//********************************************
lemma "S-SPLIT" self::barrier(c,t,0)<p> & 0<c<=t & c=c1+c2 & 0<c1<t & 0<c2<t -> self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p>;

//combine successfully
lemma "S-COMBINE" self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p> -> self::barrier(c1+c2,t,0)<p>;

//detect inconsistency
 lemma "S-FAIL" self::barrier(c1,t,0)<p1> * self::barrier(c2,t,0)<p2> & p1!=p2 & flow __norm -> true & flow __Fail;
//********************************************

// WRAPPER FUNCTION
void destroyBarrier(ref barrier b)
  requires b::barrier(c,t,0)<_> & c=t
  ensures b'=null;//'

// WRAPPER FUNCTION
barrier newBarrier(int bound)
  requires bound>0
  ensures res::barrier(bound,bound,0)<0>;

// WRAPPER FUNCTION
void waitBarrier(barrier b)
  requires b::barrier(c,t,0)<p> & c=1
  ensures b::barrier(c,t,0)<p+1>;
//********************************************

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
void SlaveStart(barrier b)
  requires  b::barrier(1,2,0)<p>
  ensures b::barrier(1,2,0)<p+5>;
{
  //initialize data
  //...
  find_my_initial_bodies(b);
  //...
  int i=0;
  //ignore the while loop to terminate based on time
  stepsystem(b);
  //
}

void main()
  requires true
  ensures true;
{
  barrier b;
  int NPROC=2;
  initparam();
  startrun(b,NPROC);//create barrier with NPROC parties
  initoutput();
  tab_init();
  //
  int id1 = fork(SlaveStart,b);
  int id2 = fork(SlaveStart,b);
  //
  join(id1);
  join(id2);
  destroyBarrier(b);
}
