/*
  This is a simplified version of the "volrend" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/
 */


hip_include '../../../../../barrier_static_header.ss'


//adaptive.C
void Ray_Trace_Non_Adaptively() requires true ensures true;

//adaptive.C
void Interpolate_Recursively() requires true ensures true;

//adaptive.C
void Ray_Trace_Adaptively() requires true ensures true;

//raytrace.C
void Pre_Shade() requires true ensures true;

//adaptive.C
void Ray_Trace(barrier TimeBarrier, int adaptive, int highest_sampling_boxlen)
  requires TimeBarrier::barrier(1,2,0)<p>
  ensures  TimeBarrier::barrier(1,2,0)<p+5> & adaptive=0 & highest_sampling_boxlen > 1
  or TimeBarrier::barrier(1,2,0)<p+3> & adaptive=0 & highest_sampling_boxlen <= 1
  or TimeBarrier::barrier(1,2,0)<p+3> & adaptive!=0;
{
  //initializing data
  //...
  /* Compute inverse Jacobian matrix from                              */
  //...
  /* Compute multiplicative inverse of inverse Jacobian matrix.        */
  //...
  /* Invoke adaptive or non-adaptive ray tracer                          */
  if (adaptive==0) {
    waitBarrier(TimeBarrier);//+1
    //...timing
    Pre_Shade();
    //...
    Ray_Trace_Adaptively();
    //...
    waitBarrier(TimeBarrier);//+1
    //...
    if (highest_sampling_boxlen > 1) {
      waitBarrier(TimeBarrier);//+1
      //...timing
      Interpolate_Recursively();
      //...timing
      waitBarrier(TimeBarrier); //+1
    }

  }else{
    waitBarrier(TimeBarrier);//+1
    //...timing
    Pre_Shade();
    //...
    Ray_Trace_Non_Adaptively();
    //...timing
    waitBarrier(TimeBarrier); //+1
    //...timing
  }
  waitBarrier(TimeBarrier); //+1
}

//render.C
void Render(barrier TimeBarrier, int adaptive, int highest_sampling_boxlen)
  requires TimeBarrier::barrier(1,2,0)<p>
  ensures  TimeBarrier::barrier(1,2,0)<p+5> & adaptive=0 & highest_sampling_boxlen > 1
  or TimeBarrier::barrier(1,2,0)<p+3> & adaptive=0 & highest_sampling_boxlen <= 1
  or TimeBarrier::barrier(1,2,0)<p+3> & adaptive!=0;
{
  //...
  Ray_Trace(TimeBarrier,adaptive,highest_sampling_boxlen);
}

//main.C
void Render_Loop( barrier TimeBarrier, barrier SlaveBarrier, int adaptive, int highest_sampling_boxlen,int ROTATE_STEPS)
  requires TimeBarrier::barrier(1,2,0)<p> * SlaveBarrier::barrier(1,2,0)<pt> & TimeBarrier!=SlaveBarrier & ROTATE_STEPS>0
  ensures  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive=0 & highest_sampling_boxlen > 1 & p1=p+5*ROTATE_STEPS & pt1=pt+2*ROTATE_STEPS
           or  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive=0 & highest_sampling_boxlen <= 1 & p1=p+3*ROTATE_STEPS & pt1=pt+2*ROTATE_STEPS
           or  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive!=0 & p1=p+3*ROTATE_STEPS & pt1=pt+2*ROTATE_STEPS;
{
  //initialize local variables
  //...

  //...
  //Assume that DIM is turn of
  int i=0;
  while(i<ROTATE_STEPS)
    requires TimeBarrier::barrier(1,2,0)<p> * SlaveBarrier::barrier(1,2,0)<pt> & TimeBarrier!=SlaveBarrier
      ensures  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive=0 & highest_sampling_boxlen > 1 & p1=p+5*(i'-i) & i<ROTATE_STEPS & i'=ROTATE_STEPS & TimeBarrier'=TimeBarrier & pt1=pt+2*(i'-i) & SlaveBarrier'=SlaveBarrier
             or  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive=0 & highest_sampling_boxlen <= 1 & p1=p+3*(i'-i) & i<ROTATE_STEPS & i'=ROTATE_STEPS & TimeBarrier'=TimeBarrier & pt1=pt+2*(i'-i) & SlaveBarrier'=SlaveBarrier
             or  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & adaptive!=0 & p1=p+3*(i'-i) & i<ROTATE_STEPS & i'=ROTATE_STEPS & TimeBarrier'=TimeBarrier & pt1=pt+2*(i'-i) & SlaveBarrier'=SlaveBarrier
             or  SlaveBarrier::barrier(1,2,0)<pt1> * TimeBarrier::barrier(1,2,0)<p1> & p1=p & i>=ROTATE_STEPS & i'=i & TimeBarrier'=TimeBarrier & adaptive'=adaptive & pt1=pt & SlaveBarrier'=SlaveBarrier;//'
  {
    waitBarrier(SlaveBarrier);//+1
    //...
    waitBarrier(SlaveBarrier);//+1
    //...
    Render(TimeBarrier,adaptive,highest_sampling_boxlen);
    //...
    i=i+1;
  }
  //...
}

//map.C
void Deallocate_Map() requires true ensures true;

//main.C
void Allocate_MImage() requires true ensures true;

//octree.C
void Load_Octree() requires true ensures true;

//octree.C
void Or_Neighbors_In_Base(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(1,2,0)<p>
  ensures SlaveBarrier::barrier(1,2,0)<p1> & p1=p+1;
{
  //do the computation
  //...
  waitBarrier(SlaveBarrier);//+1
}

//octree.C
void Compute_Base(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(1,2,0)<p>
  ensures SlaveBarrier::barrier(1,2,0)<p1> & p1=p+1;
{
  //do the computation
  //...
  waitBarrier(SlaveBarrier);//+1
}

void Allocate_Pyramid_Level() requires true ensures true;

//octree.C
void Compute_Octree(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(2,2,0)<p> 
  ensures  SlaveBarrier::barrier(2,2,0)<p1> & p1=p+2;
{
  //...
  Allocate_Pyramid_Level();
  //...
  int id1 = fork(Compute_Base,SlaveBarrier);//+1
  int id2 = fork(Compute_Base,SlaveBarrier);//
  join(id1);
  join(id2);
  //...

  id1 = fork(Or_Neighbors_In_Base,SlaveBarrier);//+1
  id2 = fork(Or_Neighbors_In_Base,SlaveBarrier);//
  join(id1);
  join(id2);
  //..
}

//main.C
void Lallocate_Image() requires true ensures true;

//main.C
void Allocate_Image() requires true ensures true;

//main.C
void Allocate_Shading_Table() requires true ensures true;

//view.C
void Compute_Pre_View() requires true ensures true;

//opacity.C
void Allocate_Opacity() requires true ensures true;

//opacity.C
void Load_Opacity() requires true ensures true;
{
  //...
  Allocate_Opacity();
  //...
}

//opacity.C
void Store_Opacity() requires true ensures true;

//opacity.C
void Opacity_Compute(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(1,2,0)<p>
  ensures SlaveBarrier::barrier(1,2,0)<p1> & p1=p+1;
{
  //do the computation
  //...
  waitBarrier(SlaveBarrier);//+1
}

//opacity.C
void Compute_Opacity(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(2,2,0)<p> 
  ensures  SlaveBarrier::barrier(2,2,0)<p1> & p1=p+1;
{
  //...
  Allocate_Opacity();
  //...
  int id1 = fork(Opacity_Compute,SlaveBarrier);//+1
  int id2 = fork(Opacity_Compute,SlaveBarrier);//+1
  join(id1);
  join(id2);
}

//normal.C
void Store_Normal() requires true ensures true;

//normal.C
void Normal_Compute(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(1,2,0)<p>
  ensures SlaveBarrier::barrier(1,2,0)<p1> & p1=p+1;
{
  //do the computation
  //...
  waitBarrier(SlaveBarrier);//+1
}

//normal.C
void Allocate_Normal() requires true ensures true;

//normal.C
void Load_Normal() requires true ensures true;
{
  //...
  Allocate_Normal();
  //...
}

//normal.C
void Compute_Normal(barrier SlaveBarrier)
  requires SlaveBarrier::barrier(2,2,0)<p> 
  ensures  SlaveBarrier::barrier(2,2,0)<p1> & p1=p+1;
{
  //...
  Allocate_Normal();
  //...
  int id1 = fork(Normal_Compute,SlaveBarrier);//+1
  int id2 = fork(Normal_Compute,SlaveBarrier);//+1
  join(id1);
  join(id2);
}

//map.C
void Allocate_Map() requires true ensures true;

//map.C
void Load_Map() requires true ensures true;
{
  //loading data
  //...
  Allocate_Map();
  //...
}

//main.C
void Init_Decomposition(int num_nodes) requires true ensures true;
{
  /* figure out what to divide dimensions of image and volume by to */
  /* partition data and computation to processors                   */
  if (num_nodes == 1) {
    //initialize for sequential program
    ;
  }else{
    //initialize for parallel program
    ;
  }
}


//option.C
void Init_Parallelization() requires true ensures true;

//option.C
void Init_Lighting() requires true ensures true;

//option.C
void Init_Opacity() requires true ensures true;

//option.C
void Init_Options(ref int highest_sampling_boxlen, int HBOXLEN) requires true ensures highest_sampling_boxlen'=HBOXLEN;//'
{
  //...
  Init_Opacity();
  Init_Lighting();

  //...
  Init_Parallelization();

  //...
  highest_sampling_boxlen = HBOXLEN; 
  /* this must be less than BLOCK_LEN */
  /* and both must be powers of 2     */
  //...
}

int random() requires true ensures true;

//assuming input=2
int getAdaptive()
  requires true
  ensures true;
{
  return random();//assuming random adaptive
}

//assuming input=2
int getNumNodes()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}

//assuming input>0
int getRotateSteps()
  requires true
  ensures res>0;
{
  int steps;
  assume(steps'>0);//'
  return steps;
}

//main.C
 void Frame(ref barrier TimeBarrier, ref barrier SlaveBarrier, int adaptive, int num_nodes, ref int id1, ref int id2, ref int highest_sampling_boxlen, int HBOXLEN,int ROTATE_STEPS)
  requires ROTATE_STEPS>0 & num_nodes=2
  ensures  SlaveBarrier'::barrier(2,2,0)<pt1> * TimeBarrier'::barrier(2,2,0)<p1> & adaptive=0 & highest_sampling_boxlen' > 1 & p1=5*ROTATE_STEPS & pt1=4+2*ROTATE_STEPS & highest_sampling_boxlen'=HBOXLEN
           or  SlaveBarrier'::barrier(2,2,0)<pt1> * TimeBarrier'::barrier(2,2,0)<p1> & adaptive=0 & highest_sampling_boxlen' <= 1 & p1=3*ROTATE_STEPS & pt1=4+2*ROTATE_STEPS & highest_sampling_boxlen'=HBOXLEN
           or  SlaveBarrier'::barrier(2,2,0)<pt1> * TimeBarrier'::barrier(2,2,0)<p1> & adaptive!=0 & p1=3*ROTATE_STEPS & pt1=4+2*ROTATE_STEPS & highest_sampling_boxlen'=HBOXLEN;//'
{
  Init_Options(highest_sampling_boxlen,HBOXLEN);
  //...
  Init_Decomposition(num_nodes);
  //...
  SlaveBarrier = newBarrier(num_nodes);
  TimeBarrier = newBarrier(num_nodes);

  //...
  /* load dataset from file to each node */
  //...
  Load_Map();
  //...
  Compute_Normal(SlaveBarrier);//+1
  Store_Normal();
  Load_Normal();
  //...
  Compute_Opacity(SlaveBarrier);//+1
  Store_Opacity();
  Load_Opacity();
  //...

  Compute_Pre_View();
  //...
  Allocate_Shading_Table();
  //...
  Allocate_Image();
  if (num_nodes == 1) {
    //initialize data
    ;
  }
  else {
    //...
    Lallocate_Image();
  }

  //...
  Compute_Octree(SlaveBarrier);//+2
  Load_Octree();

  if (adaptive==0) {
    //...
    Allocate_MImage();
    if (num_nodes == 1){
      //initialize data
      ;
    }else{
      Lallocate_Image();
    }
  }
  Deallocate_Map();
  //..

  id1 = fork(Render_Loop,TimeBarrier, SlaveBarrier, adaptive, highest_sampling_boxlen,ROTATE_STEPS);
  id2 = fork(Render_Loop,TimeBarrier, SlaveBarrier,adaptive, highest_sampling_boxlen,ROTATE_STEPS);

  //...
  join(id1);
  join(id2);
}

//main.C
void main()
  requires true
  ensures true;
{
  // read input from command lines
  int ROTATE_STEPS;
  int HBOXLEN=4;
  int highest_sampling_boxlen;
  int num_nodes ;
  barrier TimeBarrier, SlaveBarrier;
  int adaptive;

  ROTATE_STEPS = getRotateSteps();
  num_nodes = getNumNodes(); //get num_nodes from the command line arguments
  adaptive = getAdaptive();
  //...

  int id1,id2;
  Frame(TimeBarrier, SlaveBarrier, adaptive, num_nodes, id1, id2,highest_sampling_boxlen, HBOXLEN,ROTATE_STEPS);

  //...move join() into Frame
  //
  destroyBarrier(TimeBarrier);
  destroyBarrier(SlaveBarrier);
  //...
}
