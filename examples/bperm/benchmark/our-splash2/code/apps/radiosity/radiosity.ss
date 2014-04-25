/*
  This is a simplified version of the "radiosity" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/

  We would NOT be able to capture this program
  because we would not be able to verify
  when the program converges.
  That is, we couldnot determine how many steps
  (i.e. barrier waits) a program takes to converge.
  [FUTURE WORK] Related functional correctness
  with barrier phase numbers.
 */


hip_include '../../../../../barrier_static_header.ss'


/***************************************************************************
 *
 *    radiosity_converged()
 *
 *    Return TRUE(1) when the average radiosity value is converged.
 *
 ****************************************************************************/
//elemman.C
int radiosity_converged() requires true ensures true;

/*
  [FUTURE WORK]
  This procedure is tricky to capture.
  It is important to relate functional correctness
  of this procedures with the barrier's phase number
 */
//rad_main.C
bool init_ray_tasks() requires true ensures true;
{
  int conv;
  //...
  /* Check radiosity convergence */
  conv = radiosity_converged() ;
  //...
  /* If radiosity converged, then return 0 */
  if( conv==1 )
    return( false ) ;
  return (true);
}


/***************************************
 *
 *    radiosity()  Radiosity task main
 *
 ****************************************/
//rad_main.C
//FAIL
void radiosity(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+4;
{
  //initializing some data
  //...
  /* Decompose model objects into patches and build the BSP tree */
  /* Create the initial tasks */
  init_modeling_tasks() ;
  process_tasks(barr) ;//+1
  /* Gather rays & do BF refinement */
  while(init_ray_tasks())
    requires true ensures true;
  {
    /* Wait till tasks are put in the queue */
    waitBarrier(barr);//+1
    /* Then perform ray-gathering and BF-refinement till the
       solution converges */
    process_tasks(barr) ;//+1
  }
  //...
  waitBarrier(barr);//+1

  /* Compute area-weighted radiosity value at each vertex */
  init_radavg_tasks() ;
  process_tasks(barr);//+1

  /* Then normalize the radiosity at vertices */
  init_radavg_tasks() ;
  process_tasks(barr) ;//+1
  //finalizing ...
  //...
}


/***************************************************************************
 *
 *    init_radavg_tasks()
 *
 *    Create initial tasks to perform radiosity averaging.
 *
 ****************************************************************************/
//rad_main.C
void init_radavg_tasks() requires true ensures true;


//taskman.C
void process_tasks(barrier barr)
  requires barr::barrier(1,2,0)<p>
  ensures barr::barrier(1,2,0)<p1> & p1=p+1;
{
  //...
  waitBarrier(barr);
}

/***************************************************************************
 *
 *    init_modeling_tasks()
 *
 *    Initialize modeling task.
 *
 ****************************************************************************/
//modelman.C
void init_modeling_tasks() requires true ensures true;

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
void init_stat_info() requires true ensures true;


/***************************************************************************
*
*    init_edge()
  *
  *    Initialize Edge buffer.
  *    This routine must be called in single process state.
  *
  ****************************************************************************/
//smallobj.C
void init_edge() requires true ensures true;


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
void init_elemlist() requires true ensures true;

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
void init_global(ref barrier barr, int n_processors)
  requires n_processors>0
  ensures barr'::barrier(n_processors,n_processors,0)<0>;//'
{
  //initlizing data ...
  //...
  /* Initialize the barrier */
  barr = newBarrier(n_processors);
  //...
  /* Initialize task queue */
  init_taskq() ;
  /* Initialize Patch, Element, Interaction free lists */
  init_patchlist() ;
  init_elemlist() ;
  init_interactionlist();
  init_elemvertex() ;
  init_edge() ;

  /* Initialize statistical info */
  init_stat_info() ;
}


int random() requires true ensures (exists v: res=v);

//assuming input is random
int input() requires true ensures true;
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
  init_visibility_module() ;

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
    /* Start notification loop */
    // empty invocation to glibdumb/glib.c
    /* g_start( expose_callback, N_SLIDERS, sliders, N_CHOICES, choices ) ; */
    ;
  }
  //...
  destroyBarrier(barr);
  //...
}
