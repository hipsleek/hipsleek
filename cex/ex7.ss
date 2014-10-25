
checkentail 


pred_prim cex<x:set[list[int]]>
  inv true;

pred_prim state<x:list[int]> inv true;

pred_prim add<int> inv true;

global cex cx;
global state st;

void inf_loop()
  // every failure must have at least one counter-example
  requires cx::cex{[#inf_loop]} & Loop 
  ensures false; // []

//counter-examples may be split
// but can this be done across conditional?
// guided by the control path if_n or else_n
// lemma self::cex<S1 U S2> <-> self::cex<S1> * self::cex<S2>

lemma self::cex<S> * self::filter<i> <-> self::cex<{S filterNot i> 

// we provide a predicate to track the flow of code
// this state predicate may be updated as follows
lemma self::state<L1> * self::add<i> --> self::state<L1++[i]>

bool randbool()
  requires Term[]
  ensures true;

// every declared counter-example must be present
void loop(int x)
  requires cx::cex{[#loop,#if_2,#inf_loop]} & MayLoop 
  ensures false;
{
  //st::state<[#loop] * cx::cex{[#loop,#if_2,#inf_loop] & MayLoop 
  if (true) 
      //st::state<[#loop,#if_1] * cx::cex{[#loop,#if_2,#inf_loop] & MayLoop & x>0 
    x=x+1;
      //st::state<[#loop,#if_1] * cx::cex{[#loop,#if_2,#inf_loop] & MayLoop & x>0 & x'=x+1 
  else 
      //st::state<[#loop,#el_1] * cx::cex{[#loop,#if_2,#inf_loop] & MayLoop & x>0 & x'=x+1 
    x=x+2;
      //st::state<[#loop,#el_1] * cx::cex{[#loop,#if_2,#inf_loop] & MayLoop & x>0 & x'=x+2 
  //st::state<[#loop] * cx::cex{[#loop,#if_2,#inf_loop]} & MayLoop & x>0 x>0 & x'=x+1 
  // \/ st::state<[#loop] * cx::cex{[#loop,#if_2,#inf_loop]} & MayLoop & x>0 & x'=x+2
  if (rand_bool()) 
    //st::state<[#loop,#if_2] * cx::cex{[#loop,#if_2,#inf_loop]} & MayLoop & x>0 x>0 & x'=x+1 
    // \/ st::state<[#loop,#if_2] * cx::cex{{[#loop,#if_2,#inf_loop]} & MayLoop & x>0 & x'=x+2
    inf_loop();
    //st::state<[#loop,#el_2] * cx::cex{} & MayLoop & x>0 x>0 & x'=x+1 
    // \/ st::state<[#loop,#el_2] * cx::cex{} & MayLoop & x>0 & x'=x+2
  else
    //st::state<[#loop,#el_2] * cx::cex{} & MayLoop & x>0 x>0 & x'=x+1 
    // \/ st::state<[#loop,#el_2] * cx::cex{} & MayLoop & x>0 & x'=x+2
    skip;


}

/*

        S1 subseteq L1++S2
 ---- -----------------------------------------
   st::state<L1>*cx::cex<S1> |- cx::cex<S2>
     --> st::state<L1>*cx::cex<{}>

*/
