/*
  This is a simplified version of the "fmm" program
  in SPLASH-2 benchmark.
  http://www.capsl.udel.edu/splash/
 */


hip_include 'barrier_static_header.ss'


//construct_grid.C
void DestroyGrid () requires true ensures true;

//fmm.C
void
StepSimulation(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+1>;
{
  //...
  PartitionIterate();
  //...
  PartitionIterate();
  //...
  waitBarrier(synch); //+1
  //...
  PartitionIterate();
  //...
  PartitionIterate();
  //finalizing...
}

//partition_grid.C
void InsertBoxInPartition() requires true ensures true;

//cost_zones.C
void
CostZonesHelper()
  requires true
  ensures true;
{
  //...
  InsertBoxInPartition();
  //...
}
//cost_zones.C
void
CostZones (barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+2>;
{
  PartitionIterate();
  waitBarrier(synch); //+1
  //processing...
  InitPartition();
  CostZonesHelper();
  waitBarrier(synch); //+1
}

//fmm.C
void
PartitionGrid(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+2>;
{
  //...
  CostZones(synch); //+2
  //...
}

/*
 *  PrintGrid (long my_id)
 *
 *  Args : none.
 *
 *  Returns : nothing.
 *
 *  Side Effects : Prints the entire box structure of the grid to stdout.
 *
 */
//construct_grid.C
void
PrintGrid (barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+3>;
{
  //...
  waitBarrier(synch); //+1
  //...
  waitBarrier(synch); //+1
  //...
  waitBarrier(synch); //+1
  //...
}

//partition_grid.C
void PartitionIterate() requires true ensures true;

//construct_grid.C
void
ConstructLists(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+1>;
{
  //...
  PartitionIterate();
  waitBarrier(synch); //+1
  PartitionIterate();
  //...
}

//construct_grid.C
void CleanupGrid () requires true ensures true;

//construct_grid.C
void MLGHelper () requires true ensures true;

//construct_grid.C
void MergeLocalGrid () requires true ensures true;
{
  MLGHelper();
}

//construct_grid.C
void ConstructLocalGrid () requires true ensures true;

//partition_grid.C
void InitPartition () requires true ensures true;

//box.C
void FreeBoxes () requires true ensures true;

/* Each processor writes its best to a global
   array, then they read everyone else's and find the absolute best. */
//construct_grid.C
void
MergeLocalGridSize(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+1>;
{
  //initializing ...
  waitBarrier(synch);//+1
  //computing ...
}
//construct_grid.C
void DetermineLocalGridSize () requires true ensures true;

//construct_grid.C
void
DetermineGridSize(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+1>;
{
  DetermineLocalGridSize();
  MergeLocalGridSize(synch);//+1
}

//construct_grid.C
void
ConstructGrid(barrier synch)
  requires synch::barrier(1,2,0)<p>
  ensures synch::barrier(1,2,0)<p+2>;
{
  //...
  DetermineGridSize(synch);//+1
  FreeBoxes();
  InitPartition();
  //..
  ConstructLocalGrid();
  MergeLocalGrid();
  waitBarrier(synch);//+1
  CleanupGrid();
  //...
}


//box.C
void
ZeroBox ()
  requires true
  ensures true;
{
  //creating zero box
  //...
  ;
}

//box.C
void
CreateBoxes(int num_boxes)
  requires true
  ensures true;
{
  //creating box
  //...
  int i=0;
  while(i<num_boxes)
    requires true
    ensures true;
  {
    ZeroBox();
  }
}


//particle.C
void
InitParticleList()
  requires true
  ensures true;
{
  //initializing
  //...
  ;
}

//particle.C
void
CreateParticleList()
  requires true
  ensures true;
{
  //creating
  //...
  ;
}

int random() requires true ensures res>0;

int
generateNumBoxes()
  requires true
  ensures (exists i: res=i);
{
  //some math to create numBoxes
  //...
  return random();//assume ramdom
}

void ParallelExecute(barrier synch,int time_steps)
  requires synch::barrier(1,2,0)<p> & time_steps>0
  ensures synch::barrier(1,2,0)<p1> & p1=p+4+6*time_steps;
{
  //initializaing data
  int num_boxes;
  //... other data
  waitBarrier(synch);//+1
  //..
  CreateParticleList();
  InitParticleList();
  //...
  num_boxes = generateNumBoxes();
  CreateBoxes(num_boxes);
  //...
  waitBarrier(synch);//+1
  //...
  //////////////Time_Steps WHILE LOOP;
  //...
  int i=0;
  //RUN in time_steps
  while(i<time_steps)
    requires synch::barrier(1,2,0)<p>
    ensures synch::barrier(1,2,0)<p1> & p1=p+6*(i'-i) & i<time_steps & i'=time_steps & synch'=synch
         or synch::barrier(1,2,0)<p1> & p1=p & i>=time_steps & i'=i & synch'=synch; //'
  {
    //...
    ConstructGrid(synch); //+2
    ConstructLists(synch); //+1
    PartitionGrid(synch);//+2
    StepSimulation(synch);// +1
    DestroyGrid();
    //...
    i=i+1;
  }
  waitBarrier(synch);//+1
  //some timing
  //...
  waitBarrier(synch);//+1
}

//particle.C
void CreateDistribution ()
  requires true
  ensures true;
{
  //creating
  //...
  ;
}

//interactions.C
void
InitExpTables ()
  requires true
  ensures true;
{
  //initializing
  //...
  ;
}

/*
 *  InitGlobalMemory ()
 *
 *  Args : none.
 *
 *  Returns : nothing.
 *
 *  Side Effects : Allocates all the global storage for G_Memory.
 *
 */
//memory.C
void
InitGlobalMemory (ref barrier synch,int Number_Of_Processors)
  requires Number_Of_Processors>0
  ensures synch'::barrier(Number_Of_Processors,Number_Of_Processors,0)<0>;//'
{
  //initialize others
  //...
  synch = newBarrier(Number_Of_Processors);
  //initialize others
  //...
}

//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}

void
GetArguments(ref int Number_Of_Processors)
  requires true
  ensures Number_Of_Processors'=2;//'
{
  //get inputs
  //...
  Number_Of_Processors=gets();
  //get other inputs
  //...
}

void main()
  requires true
  ensures true;
{
  //...
  barrier synch;
  int Number_Of_Processors;
  int time_steps = random(); // assume lexical timestep
  //...
  GetArguments(Number_Of_Processors); //decide Number_Of_Processors
  InitGlobalMemory(synch,Number_Of_Processors);
  InitExpTables();
  CreateDistribution();
  //
  int id1 = fork(ParallelExecute,synch,time_steps);
  int id2 = fork(ParallelExecute,synch,time_steps);
  //
  join(id1);
  join(id2);
  destroyBarrier(synch);
}
