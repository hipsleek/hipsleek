/*
  This is a simplified version of the "ocean" program
  in SPLASH-2 benchmark.
  We are using the "ocean" version with:
  - non_contiguous_partitions
  - 1 barrier

  http://www.capsl.udel.edu/splash/
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

//jacobcalc.C
void jacobcalc() requires true ensures true;

//laplacalc.C
void laplacalc() requires true ensures true;

//Note that even though conceptually there 
//are 10 phases. In the implementation,
// there are total 11 phases (there are
// 2 barrier waits between phase 8 and 9
//slave2.C
void slave2(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+11;
{
  //initlizing ...
  //...
  /*   ***************************************************************

       f i r s t     p h a s e   (of timestep calculation)

  ***************************************************************/
  //...
  waitBarrier(barr);//+1
  //...
  laplacalc();
  //...
  /*     *******************************************************

         s e c o n d   p h a s e

         *******************************************************

         set values of psi{1,3} to psim{1,3}   */
  //...
  laplacalc();
  //...
  waitBarrier(barr);//+1
  /* 	*******************************************************

        t h i r d   p h a s e

        *******************************************************

        put the jacobian of the work1{1,2} and psi{1,3} arrays
        (the latter currently in temparray) in the work5{1,2} arrays  */
  //...
  waitBarrier(barr);//+1
  //...
  laplacalc();
  //...
  /*     *******************************************************

         f o u r t h   p h a s e

         *******************************************************

         put the jacobian of the work2 and work3 arrays in the work6
         array  */
  jacobcalc();
  //...
  laplacalc();
  //...
  waitBarrier(barr);//+1
  /*     *******************************************************

         f i f t h   p h a s e

         *******************************************************

         use the values of the work5, work6 and work7 arrays
         computed in the previous time-steps to compute the
         ga and gb arrays   */
  //...
  waitBarrier(barr);//+1
  /*     *******************************************************

         s i x t h   p h a s e

         *******************************************************  */
  //...
  waitBarrier(barr);//+1
  /*     *******************************************************

         s e v e n t h   p h a s e

         *******************************************************

         every process computes the running sum for its assigned portion
         in a private variable psiaipriv   */
  //...
  waitBarrier(barr);//+1
  /*      *******************************************************

          e i g h t h   p h a s e

          *******************************************************

          augment ga(i,j) with [-psiai/psibi]*psib(i,j)

          %%%%%%%%%%%%%%% f4 should be private  */
  //...
  waitBarrier(barr);//+1
  //...
  waitBarrier(barr);//+1
 /*      *******************************************************

                 n i n t h   p h a s e

 *******************************************************/
  //...
  waitBarrier(barr);//+1
  /*      *******************************************************

          t e n t h    p h a s e

  *******************************************************/
  //...
  waitBarrier(barr);//+1
}

//multi.C
void relax() requires true ensures true;

//multi.C
void multig(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+4;
{
  //initlizing ...
  //...
  /* barrier to make sure all procs have finished intadd or rescal   */
  /* before proceeding with relaxation                               */
  waitBarrier(barr);//+1
  relax();
  /* barrier to make sure all red computations have been performed   */
  waitBarrier(barr);//+1
  relax();
  //...
  /* barrier to make sure all processors have checked local error    */
  waitBarrier(barr);//+1
  //..
  /* barrier to make sure master does not cycle back to top of loop  */
  /* and reset global->err before we read it and decide what to do   */
  waitBarrier(barr);//+1
  //..
}

//slave1.C
void slave(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+19;
{
  //initializing data ...
  //...
  /* wait until all processes have completed the above initialization  */
  waitBarrier(barr);//+1
  //...
  waitBarrier(barr);//+1
  multig(barr);//+4
  //...
  waitBarrier(barr);//+1
  /* update the local running sum psibipriv by summing all the resulting
     values in that process's share of the psib matrix   */
  //...
  /* update the shared variable psibi by summing all the psibiprivs
     of the individual processes into it.  note that this combined
     private and shared sum method avoids accessing the shared
     variable psibi once for every element of the matrix.  */
  //...
  /* initialize psi matrices the same way  */
  //...
  /* compute input curl of wind stress */
  //...
  waitBarrier(barr);//+1
  /***************************************************************
  one-time stuff over at this point
  ***************************************************************/
  //...
  slave2(barr);//+11
  //...
  /* update values of psilm array to psilm + psim[2]  */
  //...
}


//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}

void main()
  requires true
  ensures true;
{
  // initialization ...
  int nprocs = gets();
  barrier barr = newBarrier(nprocs);
  //...
  /* Determine starting coord and number of points to process in     */
  /* each direction                                                  */
  //...
  /* initialize constants and variables
     id is a global shared variable that has fetch-and-add operations
     performed on it by processes to obtain their pids.   */
  int id1 = fork(slave,barr);
  int id2 = fork(slave,barr);
  //
  join(id1);
  join(id2);
  //finalizing...
  destroyBarrier(barr);
}
