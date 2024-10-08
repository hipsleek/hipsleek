/*
  This is a simplified version of the "water-nsquared" program
  in SPLASH-2 benchmark.
  http://www.capsl.udel.edu/splash/
 */


hip_include '../../../../../barrier_static_header.ss'


/* routine that implements the time-steps. Called by main routine and calls others */
//mdmain.C
void MDMAIN(barrier start,barrier InterfBar,barrier PotengBar,int NSTEP,int NSAVE,int NPRINT)
  requires start::barrier(1,2,0)<pt> * InterfBar::barrier(1,2,0)<pi> * PotengBar::barrier(1,2,0)<pp> & NSTEP>=1 & NSAVE >=1 & NPRINT>=1 & start!=InterfBar & InterfBar!=PotengBar & start!=PotengBar
  ensures start::barrier(1,2,0)<pt1> * InterfBar::barrier(1,2,0)<pi1> * PotengBar::barrier(1,2,0)<pp1> & pt1=pt+2+5*NSTEP & pi1=pi+1+NSTEP & pp1=pp+NSTEP;
{
  //...
  /*.......ESTIMATE ACCELERATION FROM F/M */
  INTRAF();

  waitBarrier(start);//+1

  INTERF(InterfBar);//+1

  waitBarrier(start);//+1

  /* MOLECULAR DYNAMICS LOOP OVER ALL TIME-STEPS */
  int i=0;
  while (i < NSTEP)
    requires start::barrier(1,2,0)<pt> * InterfBar::barrier(1,2,0)<pi> * PotengBar::barrier(1,2,0)<pp> & start!=InterfBar & InterfBar!=PotengBar & start!=PotengBar
    ensures start::barrier(1,2,0)<pt1> * InterfBar::barrier(1,2,0)<pi1> * PotengBar::barrier(1,2,0)<pp1> & i<NSTEP & i'=NSTEP & pt1=pt+5*(i'-i) & pi1=pi+i'-i & pp1=pp+i'-i & start'=start & InterfBar'=InterfBar & PotengBar'=PotengBar
           or start::barrier(1,2,0)<pt> * InterfBar::barrier(1,2,0)<pi> * PotengBar::barrier(1,2,0)<pp> & i>=NSTEP & i'=i & start'=start & InterfBar'=InterfBar & PotengBar'=PotengBar; //'
  {
    /* reset simulator stats at beginning of second time-step */
    //...

    /* initialize various shared sums */
    //...

    waitBarrier(start);//+1
    PREDIC();
    INTRAF();
    waitBarrier(start);//+1

    //...

    INTERF(InterfBar);//+1

    //...

    CORREC();

    BNDRY();

    KINETI();

    waitBarrier(start);//+1

    /*  check if potential energy is to be computed, and if
        printing and/or saving is to be done, this time step.
        Note that potential energy is computed once every NPRINT
        time-steps */
    /*  Assuming that NPRINT=1, hence potential energy is computed
        in every iteration */
    //...
    /*  call potential energy computing routine */
    POTENG(PotengBar);//+1
    waitBarrier(start);//+1

    //...

    /* compute some values to print */
    //...

    /* wait for everyone to finish time-step */
    waitBarrier(start);//+1
    i++;
  }
  //..
}


//poteng.C
void POTENG(barrier PotengBar)
  requires PotengBar::barrier(1,2,0)<po>
  ensures PotengBar::barrier(1,2,0)<po+1>;
{
  /*
    this routine calculates the potential energy of the system.
    FC11 ,FC12, FC13, and FC33 are the quardratic force constants
  */
  //...

  /*  compute intra-molecular potential energy */
  //...
  
  waitBarrier(PotengBar);//+1

  /*  compute inter-molecular potential energy */
  //...

  /* update shared sums from computed  private sums */
  //...
}

  /* this routine computes kinetic energy in each of the three spatial
     dimensions, and puts the computed values in the SUM array */
  void KINETI() requires true ensures true;


/* this routine puts the molecules back inside the box if they are out */
//bndry.C
void BNDRY() requires true ensures true;


/* corrects the predicted values, based on forces etc. computed in the interim
 *
 * PCC : the predictor-corrector constants
 * NOR1: NORDER + 1 = 7 for a sixth-order method)
 */
//predcor.C
void CORREC() requires true ensures true;


/* predicts new values for displacement and its five derivatives
 *
 * NOR1 : NOR1 = NORDER + 1 = 7 (for a sixth-order method)
 */
//predcor.C
void PREDIC()
  requires true 
  ensures true;
{
  /*   this routine calculates predicted F(X), F'(X), F''(X), ... */
  //...
  ;
}

/* in this version of interf, a private force array is maintained */
/* for every process.  A process computes interactions into its   */
/* private force array, and later updates the shared destination  */
/* array with locks, but only updates those locations that it     */
/* computed something for                                         */
//interf.C
void INTERF(barrier InterfBar)
  requires InterfBar::barrier(1,2,0)<pi>
  ensures InterfBar::barrier(1,2,0)<pi+1>;
{
  /* This routine gets called both from main() and from mdmain().
     When called from main(), it is used to estimate the initial
     accelerations by computing intermolecular forces.  When called
     from mdmain(), it is used to compute intermolecular forces.
     The parameter DEST specifies whether results go into the
     accelerations or the forces. Uses routine UPDATE_FORCES in this
     file, and routine CSHIFT in file cshift.U */
  /*
    .....this routine calculates inter-molecular interaction forces
    the distances are arranged in the order  M-M, M-H1, M-H3, H1-M,
    H3-M, H1-H3, H1-H1, H3-H1, H3-H3, O-O, O-H1, O-H3, H1-O, H3-O,
    where the M are "centers" of the molecules.
  */
  // ... initializing local data
  //...

  /* initialize PFORCES array */
  //...

  /*  accumulate the running sum from private
      per-interaction partial sums   */
  //...

  /* at the end of the above force-computation, comp_last */
  /* contains the number of the last molecule (no modulo) */
  /* that this process touched                            */
  //...

  /* wait till all forces are updated */

  waitBarrier(InterfBar); //+1

  /* divide final forces by masses */
  //...

}/* end of subroutine INTERF */


//intraf.C
void INTRAF()
  requires true 
  ensures true;
{
  /*
    .....this routine calculates the intra-molecular force/mass acting on
    each atom.
    FC11, FC12, FC13, AND FC33 are the quardratic force constants
    FC111, FC112, ....... ETC. are the cubic      force constants
    FC1111, FC1112 ...... ETC. are the quartic    force constants
  */
  ;
  //...
}


/* routine that each created process starts at;
   it simply calls the timestep routine */
//water.C
void WorkStart(barrier start,barrier InterfBar,barrier PotengBar,int NSTEP,int NSAVE,int NPRINT)
  requires start::barrier(1,2,0)<pt> * InterfBar::barrier(1,2,0)<pi> * PotengBar::barrier(1,2,0)<pp> & NSTEP>=1 & NSAVE >=1 & NPRINT>=1 & start!=InterfBar & InterfBar!=PotengBar & start!=PotengBar
  ensures start::barrier(1,2,0)<pt1> * InterfBar::barrier(1,2,0)<pi1> * PotengBar::barrier(1,2,0)<pp1> & pt1=pt+2+5*NSTEP & pi1=pi+1+NSTEP & pp1=pp+NSTEP;
{
  //...
  MDMAIN(start,InterfBar,PotengBar,NSTEP,NSAVE,NPRINT);
  //...
}


/*   this routine initializes the positions of the molecules along
     a regular cubical lattice, and randomizes the initial velocities of
     the atoms.  The random numbers used in the initialization of velocities
     are read from the file random.in, which must be in the current working
     directory in which the program is run  */
//initia.C
void INITIA() requires true ensures true;


/* sets up some system constants */
//syscons.C
void SYSCNS() requires true ensures true;


/* set up some constants
 * N : NORDER + 1 = 7 for a sixth-order method
 * C : DIMENSION C(N,N)
 */
//cnstnt.C
void CNSTNT() requires true ensures true;


int random() requires true ensures res>0;


int getNPRINT()
  requires true
  ensures res>0;
{
  int i;
  assume(i'>0); //'
  return i;//assume ramdom
}


int getNSAVE()
  requires true
  ensures res>0;
{
  int i;
  assume(i'>0); //'
  return i;//assume ramdom
}


int getNSTEP()
  requires true
  ensures res>0;
{
  int i;
  assume(i'>0); //'
  return i;//assume ramdom
}


//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}


//water.C
void main()
  requires true
  ensures true;
{
  /* number of processors being used;
     run-time input           */
  int NumProcs;
  /* the number of timesteps to be simulated */
  int NSTEP;
  /* the frequency with which to compute potential energy */
  /* the frequency with which to save data in data collection */
  int NSAVE;

  int NPRINT ;
  barrier start; 
  barrier InterfBar;
  barrier PotengBar;
  /* read input */
  //...
  NumProcs = gets(); //get from input
  NSTEP = getNSTEP(); //get random NSTEP from input
  NSAVE = getNSAVE(); // >0
  NPRINT = getNPRINT(); // >0

  /* SET UP SCALING FACTORS AND CONSTANTS */
  //...
  CNSTNT(); /* sub. call to set up constants */

  /* Do memory initializations */
  //...

  /* macro calls to initialize synch varibles  */
  //...
  start =  newBarrier(NumProcs);
  InterfBar =  newBarrier(NumProcs);
  PotengBar =  newBarrier(NumProcs);
  //...

  /* set up control for static scheduling */
  //...

  SYSCNS();    /* sub. call to initialize system constants  */

  //... printf

  /* initialization routine; also reads displacements and
     sets up random velocities*/
  INITIA();

  /*.....start molecular dynamic loop */
  //...

  /* spawn helper processes, each getting its unique process id */
  int id1 = fork(WorkStart,start,InterfBar,PotengBar,NSTEP,NSAVE,NPRINT);
  int id2 = fork(WorkStart,start,InterfBar,PotengBar,NSTEP,NSAVE,NPRINT);

  /* macro to make main process wait for all others to finish */
  join(id1);
  join(id2);

  //finalization and printf
  destroyBarrier(start);
  destroyBarrier(InterfBar);
  destroyBarrier(PotengBar);
  //...
}
