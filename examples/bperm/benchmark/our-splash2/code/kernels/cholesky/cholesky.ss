/*
  This is a simplified version of the "cholesky" program
  in SPLASH-2 benchmark.

  http://www.capsl.udel.edu/splash/
 */


hip_include '../../../../../barrier_static_header.ss'


data SMatrix{}


//solve.C
void Go(barrier start)
  requires start::barrier(1,2,0)<p>
  ensures start::barrier(1,2,0)<p+4>;
{
  //initialization
  //...

  PreAllocateFO();

  /* initialize - put original non-zeroes in L */

  PreProcessFO();

  waitBarrier(start); //+1

  /* POSSIBLE ENHANCEMENT:  Here is where one might reset the
     statistics that one is measuring about the parallel execution */
  //...

  BNumericSolveFO();

  waitBarrier(start); //+1

  // other computation
  //...

  waitBarrier(start); //+1

  //...

  waitBarrier(start); //+1
}


//fo.C
void BNumericSolveFO() requires true ensures true;


//fo.C
void PreProcessFO()
  requires true ensures true;
{
  InitRemainingFO();
  InitReceivedFO();
}

//fo.C
void InitRemainingFO() requires true ensures true;


//fo.C
void InitReceivedFO() requires true ensures true;


//fo.C
void PreAllocateFO() requires true ensures true;


//fo.C
void ComputeReceivedFO() requires true ensures true;


/* determine number of updates that must be performed on each block */
//fo.C
void ComputeRemainingFO() requires true ensures true;

//fo.C
void PreAllocate1FO() requires true ensures true;


//mf.C
void InitTaskQueues(int P) requires true ensures true;


/* put original non-zero values into blocks */
//block2.C
void FillInNZ(SMatrix M) requires true ensures true;


//block2.C
void AllocateNZ() requires true ensures true;


//assign.C
void EmbedBlocks() requires true ensures true;


//assign.C
void AssignBlocksNow(int P)
  requires true
  ensures true;
{
  if (P == 1) {
    //some computation
    ;
  }else{
    EmbedBlocks();
  }
}


/* find non-zero structure of individual blocks */
//block2.C
void FillInStructure(SMatrix M) requires true ensures true;


/* perform symbolic factorization of original matrix into block form */
//block2.C
void CreateBlockedMatrix2(SMatrix M) requires true ensures true;


//bksolve.C
void CreateVector(SMatrix M) requires true ensures true;


//solve.C
void ComposePerm() requires true ensures true;


//seg.C
void NoSegments(SMatrix M) requires true ensures true;


//seg.C
void FindMaxHeight(SMatrix L) requires true ensures true;


//seg.C
void ComputeTargetBlockSize(SMatrix M, int P)
  requires true ensures true;
{
  //...
  FindMaxHeight(M);
  //...
}


void free() requires true ensures true;


//parts.C
void Partition() requires true ensures true;


//amal.C
void Amalgamate2() requires true ensures true;


//tree.C
void FindSupernodes() requires true ensures true;


//tree.C
void ComputeWorkTree() requires true ensures true;


//tree.C
void ComputeNZ() requires true ensures true;


//tree.C
void ParentToChild() requires true ensures true;


//tree.C
void EliminationTreeFromA() requires true ensures true;


//amal.C
void InvertPerm() requires true ensures true;


//seg.C
void CreatePermutation() requires true ensures true;


//util.C
SMatrix LowerToFull(SMatrix L) requires true ensures true;


//util.C
void ReadVector() requires true ensures true;


//util.C
SMatrix NewMatrix() requires true ensures true;

//util.C
void FreeMatrix(SMatrix M) requires true ensures true;


//util.C
void DumpLine() requires true ensures true;


//util.C
SMatrix ReadSparse()
  requires true ensures true;
{
  SMatrix M,F;
  //...

  DumpLine();
  //...

  DumpLine();
  //...

  DumpLine();
  //...

  M = NewMatrix();

  ReadVector();

  //...

  F = LowerToFull(M);

  //...

  FreeMatrix(M);

  return F;
}

//malloc.C
void InitOneFreeList(int p)
  requires true ensures true;
{
  //init memory pool
  ;
}


//malloc.C
void MallocInit(int P)
  requires true ensures true;
{
  //...
  int p=-1;
  while (p<P)
    requires true
    ensures true;
  {
    InitOneFreeList(p);
  }
}


//assuming input=2
int gets()
  requires true
  ensures res=2;
{
  return 2;//assuming there are 2 threads
}


//solve.C
void main()
  requires true
  ensures true;
{
  // variables declarations
  //...
  SMatrix M;
  int P; //number of threads
  barrier start;

  // read command line input
  //...
  P = gets();

  // initialization
  // ...
  start = newBarrier(P);
  //...
  MallocInit(P);

  //...

  M = ReadSparse();

  // ... printf


  CreatePermutation();

  InvertPerm();

  //...
  EliminationTreeFromA();

  //...
  ParentToChild();

  //...
  ComputeNZ();

  //...
  ComputeWorkTree();

  //...
  FindSupernodes();

  //...
  Amalgamate2();

  
  //...
  Partition();
  free();

  //...

  ComputeTargetBlockSize(M, P);

  //...

  NoSegments(M);

  //...
  CreatePermutation();
  ComposePerm();
  free();

  InvertPerm();

  CreateVector(M);
  //...
  CreateBlockedMatrix2(M);

  FillInStructure(M);

  AssignBlocksNow(P);

  AllocateNZ();

  FillInNZ(M);
  FreeMatrix(M);

  InitTaskQueues(P);

  PreAllocate1FO();
  ComputeRemainingFO();
  ComputeReceivedFO();

  int id1 = fork(Go,start);
  int id2 = fork(Go,start);
  //
  join(id1);
  join(id2);
  //finalizing...
  destroyBarrier(start);
  //printf ...
}
