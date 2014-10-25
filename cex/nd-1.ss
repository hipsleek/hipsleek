pred_prim nd_bool<x:bool>
  inv true;

pred_prim nd_int<x:int>
  inv true;

bool rand_bool()
  requires Term[]
  ensures nd_bool<res>;

int rand_int()
  requires Term[]
  ensures nd_int<res>;

// every declared counter-example must be present
void loop(int x)
  requires cx::cex{[#loop,#else_1,#loop]} & MayLoop
  ensures true; 
{
  //st::state<[#loop] * cx::cex{[#loop,#else,#loop]} 
  bool b;
  b=rand_bool();
  if (b) 
      //st::state<[#loop,#if_1] * cx::cex{}
    return;
      //st::state<[#loop,#if_1] * cx::cex{}
  else 
      //st::state<[#loop,#else_1] * cx::cex{[#loop,#else_1,#loop]}
    loop(x-1); 
      //st::state<[#loop,#else_1] * cx::cex{}
}



main()
requires cx::cex{[#main,#loop]}} & MayLoop
 ensures true;
{
  loop(-5);
}

/*

        S1 subseteq L1++S2
 ---- -----------------------------------------
   st::state<L1>*cx::cex<S1> |- cx::cex<S2>
     --> st::state<L1>*cx::cex<{}>

*/
