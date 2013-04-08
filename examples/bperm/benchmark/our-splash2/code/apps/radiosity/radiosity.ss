/*
  This is a simplified version of the "radiosity" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/

  We would NOT be able to capture this program
  because we would not be able to verify
  when the program converges.
  That is, we couldnot determine how many steps
  (i.e. barrier waits) a program takes to converge.
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

/***************************************************************************
 *
 *    radiosity_converged()
 *
 *    Return TRUE(1) when the average radiosity value is converged.
 *
 ****************************************************************************/
//elemman.C
long radiosity_converged() requires true ensures true;

//rad_main.C
long init_ray_tasks(long process_id) requires true ensures true;
{
  int conv;
  //...
  /* Check radiosity convergence */
  conv = radiosity_converged() ;
  //...
  /* If radiosity converged, then return 0 */
  if( conv )
    return( 0 ) ;
}


/***************************************
 *
 *    radiosity()  Radiosity task main
 *
 ****************************************/
//rad_main.C
void radiosity(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+4;
{
  //initializing some data
  //...
  /* Decompose model objects into patches and build the BSP tree */
  /* Create the initial tasks */
  init_modeling_tasks(process_id) ;
  process_tasks(process_id) ;
  /* Gather rays & do BF refinement */
  while( init_ray_tasks() )
    requires true ensures true;
  {
    /* Wait till tasks are put in the queue */
    waitBarrier(barr);//+1
    /* Then perform ray-gathering and BF-refinement till the
       solution converges */
    process_tasks() ;
  }
  //...
  waitBarrier(barr);//+1

  /* Compute area-weighted radiosity value at each vertex */
  init_radavg_tasks() ;
  process_tasks();

  /* Then normalize the radiosity at vertices */
  init_radavg_tasks() ;
  process_tasks() ;
  //finalizing ...
  //...
}


void init_patch_cache() requires true ensures true;

/*************************************************************
 *
 *	void init_visibility_module()
 *
 *       initialize the random test rays array.
 *
 *       Test ray parameters are precomputed as follows.
 *       (1) The triangles are divided into 16 small triangles.
 *       (2) Each small triangle shoots a ray to a small triangle on the
 *           destination. If N-rays are requested by get_test_ray(),
 *           N small triangles are chosen on the source and the destination
 *           and a ray is shot between N pairs of the small triangles.
 *       (3) Current scheme selects pairs of the small triangles in a static
 *           manner. The pairs are chosen such that rays are equally
 *           distributed.
 *
 *************************************************************/
//visible.C
void init_visibility_module()
  requires true ensures true;
{
  //initialzing triangles ...
  //...
  /* Initialize patch cache */
  init_patch_cache() ;
}

/***************************************
*
*    Initialize statistical info
*
****************************************/
//rad_tools.C
void init_stat_info(long process_id) requires true ensures true;


/***************************************************************************
*
*    init_edge()
  *
  *    Initialize Edge buffer.
  *    This routine must be called in single process state.
  *
  ****************************************************************************/
//smallobj.C
void init_edge(long process_id) requires true ensures true;


/***************************************************************************
*
*    init_elemvertex()
  *
  *    Initialize ElemVertex buffer.
  *    This routine must be called in single process state.
  *
  ****************************************************************************/
//smallobj.C
void init_elemvertex() requires true ensures true;

/***************************************************************************
 *
 *    init_interactionlist()
 *
 *    Initialize Interaction free list
 *
 ****************************************************************************/
//elemman.C
void init_interactionlist() requires true ensures true;

/***************************************************************************
 *
 *    init_elemlist()
 *
 *    Initialize Element free list
 *
 ****************************************************************************/
//elemman.C
void init_elemlist(long process_id) requires true ensures true;

/***************************************************************************
 *
 *    init_patchlist()
 *
 *    Initialize patch free list.
 *
 ****************************************************************************/
//patchman.C
void init_patchlist() requires true ensures true;

/***************************************************************************
 *
 *    init_taskq()
 *
 *    Initialize task free list and the task queue.
 *    This routine must be called when only one process is active.
 *
 ****************************************************************************/
//taskman.C
void init_taskq() requires true ensures true;


/***************************************
 *
 *    init_global()
 *
 ****************************************/
void init_global(barrier barr, int n_processors)
  requires n_processors>0
  ensures barr'::barrier(int n_processors,int n_processors,0)<0>;//'
{
  //initlizing data ...
  //...
  /* Initialize the barrier */
  barr = newBarrier(nprocs);
  //...
  /* Initialize task queue */
  init_taskq(process_id) ;
  /* Initialize Patch, Element, Interaction free lists */
  init_patchlist(process_id) ;
  init_elemlist(process_id) ;
  init_interactionlist(process_id) ;
  init_elemvertex(process_id) ;
  init_edge(process_id) ;

  /* Initialize statistical info */
  init_stat_info(process_id) ;
}


int random() requires true ensures (exists v: res=v);

//assuming input is random
int input(int ref batch_mode) requires true ensures true;
{
  return random();//assuming there are 2 threads
}


/*************************************************************
 *
 * parse_args()   Parse arguments
 *
 **************************************************************/
//rad_main.C
void parse_args(ref int n_processors, ref int batch_mode)
  requires true
  ensures n_processors'=2;//'
{
  n_processors=2; //assuming there are 2 threads
  batch_mode = input(); //read batch_mode from user input
}

//rad_main.C
void main()
  requires true
  ensures true;
{
  // initialization ...
  int n_processors;
  int batch_mode=0; //initially 0
  barrier barr;
  /* Parse arguments */
  parse_args(n_processors,batch_mode);
  //...
  init_global(barr,n_processors) ;
  //...
  /* Initial random testing rays array for visibility test. */
  init_visibility_module(0) ;

  if(batch_mode==1){
    /* In batch mode, create child processes and start immediately */
    //...
    int id1 = fork(radiosity,barr);
    int id2 = fork(radiosity,barr);
    //
    join(id1);
    join(id2);
    //finalizing...

  }else{
    /* In interactive mode, start workers, and the master starts
       notification loop */

    /* Start notification loop */
    g_start( expose_callback,
             N_SLIDERS, sliders, N_CHOICES, choices ) ;
  }
  //...
  destroyBarrier(barr);
  //...


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
