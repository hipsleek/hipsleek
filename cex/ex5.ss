pred_prim cex<x:set[list[int]]>
  inv true;

pred_prim state<x:list[int]>
  inv true;

global cex cx;
global state st;

void inf_loop()
  // every failure must have at least one counter-example
  requires cx::cex{[#inf_loop]} & Loop 
  ensures false; // []

//counter-examples may be split
// but can this be done across conditional?
lemma cx::cex<S1 U S2> <-> cx::cex<S1> * cx::cex<S2>

// we provide a predicate to track the flow of code
// this state predicate may be updated as follows
lemma state<L1> * add<L2> --> state<L1++L2>

bool randbool()
  requires Term[]
  ensures true;

// every declared counter-example must be present
void loop(int x)
 case {
  x>0 -> requires cx::cex{[#loop,#if,#inf_loop]} & Loop
         ensures false; 
  x<=0 -> requires Term[]
         ensures true; 
{
  //st::state<[#loop] * cx::cex{[#loop,#if,#inf_loop] & Loop & x>0
  //st::state<[#loop] * Term & x>0
  if (x>0) 
      //st::state<[#loop,#if] * cx::cex{[#loop,#if,#inf_loop] & Loop & x>0
      inf_loop(); 
      //false
  else 
      //st::state<[#loop,#else] & Term & x<=0
      skip; 
     //st::state<[#loop,#else] & Term & x<=0
}

/*

        S1 subseteq L1++S2
 ---- -----------------------------------------
   st::state<L1>*cx::cex<S1> |- cx::cex<S2>
     --> st::state<L1>*cx::cex<{}>

*/
