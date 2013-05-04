data pair {
  int fst;
  int snd;
}


int xZero0(int x)
  requires true
  ensures res!=0;
{

  x = x+1; //12
  pair p = new pair(x,0);
  int y = p.snd; //14
  x = x+1;
  return y;
}

/*

 path trace:    (must) cause:  res=0 |-  res!=0. LOCS:[9;13;14;16] (must-bug)

 Why do we have 9? Is it the stuff in RHS?

*/

