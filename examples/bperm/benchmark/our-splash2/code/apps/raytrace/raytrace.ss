/*
  This is a simplified version of the "raytrace" program
  in SPLASH-2 benchmark.

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

/*
 * NAME
 *	StartRayTrace - starting point for all ray tracing proceses
 *
 * SYNOPSIS
 *	VOID	StartRayTrace()
 *
 * RETURNS
 *	Nothing.
 */
//main.C
void StartRayTrace(barrier start)
  requires start::barrier(1,2,0)<p>
  ensures start::barrier(1,2,0)<p1> & p1=p+1;
{
  // initializing local data
  //...
  InitWorkPool();
  InitRayTreeStack();
  /*
   *	Wait for all processes to be created, initialize their work
   *	pools, and arrive at this point; then proceed.	This BARRIER
   *	is absolutely required.  Read comments in PutJob before
   *	moving this barrier.
   */

  waitBarrier(start);//+1
  RayTrace();
  //finalizing timing
  //...
}

/*
 * NAME
 *	InitWorkPool - fill pid's work pool with jobs
 *
 * SYNOPSIS
 *	VOID	InitWorkPool(pid)
 *	INT	pid;			// Process id to initialize.
 *
 * RETURNS
 *	Nothing.
 */
//workpool.C
void InitWorkPool() requires true ensures true;

/*
 * NAME
 *	InitRayTreeStack - initialize the ray tree stack
 *
 * SYNOPSIS
 *	VOID	InitRayTreeStack(TreeDepth,pid)
 *	INT	TreeDepth.		// Max depth of a ray tree.
 *	INT	pid.
 *
 * DESCRIPTION
 *	Initialize the ray tree stack by setting the stack pointer to 0 and
 *	allocating memory for the stack.
 *
 * RETURNS
 *	Nothing.
 */
//raystack.C
void InitRayTreeStack() requires true ensures true;

//not operate on barrier start
//trace.C
void RayTrace() requires true ensures true;

//fbuf.C
void CloseFrameBuffer() requires true ensures true;

//memory.C
void ma_print() requires true ensures true;

/*
 * NAME
 *	PrintStatistics - print out various ray tracer statistics
 *
 * SYNOPSIS
 *	VOID	PrintStatistics()
 *
 * RETURNS
 *	Nothing.
 */
//main.C
void PrintStatistics(int TraversalType, int TT_HUG) requires true ensures true;
{
  if (TraversalType == TT_HUG)
    {
      ma_print();
    }
}

//cr.C
void create_grid(int num_prims) requires true ensures true;

//cr.C
void init_world_voxel(int numelements) requires true ensures true;

//cr.C
void init_world_grid(int numelements) requires true ensures true;

//geo.C
void MakeElementArray(ref int totalElements) requires true ensures true;

/*
 * NAME
 *	init_masks - initialize empty and nonempty mask arrays
 *
 * SYNOPSIS
 *	VOID	init_masks()
 *
 * RETURNS
 *	Nothing.
 */
//cr.C
void init_masks() requires true ensures true;


/*
 * NAME
 *	BuildHierarchy_Uniform - build HU grid from model
 *
 * SYNOPSIS
 *	VOID	BuildHierarchy_Uniform()
 *
 * RETURNS
 *	Nothing.
 *
 */
//husetup.C
void BuildHierarchy_Uniform() requires true ensures true;
{
  // ... declare local variables
  int num_pe;
  init_masks();
  MakeElementArray(num_pe);

  init_world_voxel(num_pe);

  init_world_grid(num_pe);
  create_grid(num_pe);
  //...
}

/*
 * NAME
 *	CreateViewMatrix - compute view transform matrix and put in View.vtrans
 *
 * SYNOPSIS
 *	VOID	CreateViewMatrix()
 *
 * NOTES
 *	Taken from David Kurlander's program.
 *
 * RETURNS
 *	Nothing.
 */
//env.C
void CreateViewMatrix() requires true ensures true;

/*
 * NAME
 *	 OpenFrameBuffer - allocate and clear framebuffer
 *
 * SYNOPSIS
 *	 VOID	 OpenFrameBuffer()
 *
 * RETURNS
 *	Nothing.
 */
//fbuf.C
void OpenFrameBuffer() requires true ensures true;

//geo.C
void NormalizeGeo() requires true ensures true;

//matrix.C
void MatrixCopy() requires true ensures true;

//matrix.C
void MatrixInverse() requires true ensures true;

//matrix.C
void  MatrixTranspose() requires true ensures true;

/*
 * NAME
 *	ReadGeoFile - read in the geometry file
 *
 * SYNOPSIS
 *	VOID	ReadGeoFile(GeoFileName)
 *	CHAR	*GeoFileName;		// File to open.
 *
 * DESCRIPTION
 *	Read in the model file - call primitive object routines to read in
 *	their own data.  Objects are put in a linked list.
 *
 *	Transform objects by modeling transformation if any.
 *
 *	If TT_LIST traversal, ModelNorm parameter indicates whether data will
 *	be normalized.
 *
 * RETURNS
 *	Nothing.
 */
//geo.C
void ReadGeoFile() requires true ensures true;
{
  //... initializing data

  /* Retrieve model transform. */

  MatrixCopy();
  MatrixInverse();
  MatrixTranspose();
  //...
  /* Process the file data for each object. */
  //...

  NormalizeGeo();
  //...
}


/*
 * NAME
 *	InitDisplay - setup display parameters
 *
 * SYNOPSIS
 *	VOID	InitDisplay()
 *
 * RETURNS
 *	Nothing.
 */

void InitDisplay() requires true ensures true;


int getUnknownInput() requires true ensures true;

/*
 * NAME
 *	InitEnv - setup the default environment variables
 *
 * SYNOPSIS
 *	VOID	InitEnv()
 *
 * RETURNS
 *	Nothing.
 */
//env.C
void InitEnv() requires true ensures true;

/*
 * NAME
 *	ReadEnvFile - read and parse environment file
 *
 * SYNOPSIS
 *	VOID	ReadEnvFile(EnvFileName)
 *	CHAR	*EnvFileName;		// Environment filename.
 *
 * RETURNS
 *	Nothing.
 */
//env.C
void ReadEnvFile(ref int TraversalType) requires true ensures true;
{
  //... open enviroment file
  InitEnv();			/* Set defaults. */
  /* Process command file according to opcodes. */
  //...
  TraversalType= getUnknownInput(); //assume unknown input
  /* Set up screen parameters. */
  InitDisplay();
  //...
}

/*
 * NAME
 *	Huniform_defaults - setup the five HUG parameter defaults
 *
 * SYNOPSIS
 *	VOID	Huniform_defaults()
 *
 * RETURNS
 *	Nothing.
 */
//husetup.C
void Huniform_defaults() requires true ensures true;

//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}

/*
 * NAME
 *	main - mainline for the program
 *
 * SYNOPSIS
 *	INT	main(argc, argv)
 *	INT	argc;
 *	CHAR	*argv[];
 *
 * DESCRIPTION
 *	Main parses command line arguments, opens/closes the files involved,
 *	performs initializations, reads in the model database, partitions it
 *	as needed, and calls StartTraceRay() to do the work.
 *
 * RETURNS
 *	0 if successful.
 *	1 for any type of failure.
 */
//main.C
void main()
  requires true
  ensures true;
{
  int TT_HUG=1;
  int TraversalType;
  int nprocs;
  barrier start;
  /*
   *  First, process command line arguments.
   */
  //...
  nprocs = gets(); //get nprocs from the command line

  /*
   *  Perform shared environment initializations.
   */
  //...
  start = newBarrier(nprocs);
  //...
  /*
   *  Initialize HUG parameters, read environment and geometry files.
   */

  Huniform_defaults();
  ReadEnvFile(TraversalType);
  ReadGeoFile();
  OpenFrameBuffer();

  /*
   *  Compute view transform and its inverse.
   */

  CreateViewMatrix();
  MatrixCopy();
  MatrixInverse();
  MatrixCopy();

  //...
  /*
   *	Preprocess database into hierarchical uniform grid.
   */
  if (TraversalType == TT_HUG)
    BuildHierarchy_Uniform();

  /*
   *  Now create slave processes.
   */

  int id1 = fork(StartRayTrace,start);
  int id2 = fork(StartRayTrace,start);
  //

  join(id1);
  join(id2);
  //finalizing...
  destroyBarrier(start);
  /*
   *  We are finished.  Clean up, print statistics and run time.
   */

  CloseFrameBuffer();
  PrintStatistics(TraversalType,TT_HUG);
  //...
}
