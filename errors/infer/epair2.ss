data pair {
  int fst;
  int snd;
}


int xZero0(int x)
  requires true
  ensures res!=0;
{

  x = 0; //12
  pair p = new pair(x,0);
  int y = p.fst; //14
  x = x+1;
  return y;
}

/*

  path trace:    (must) cause:  res=0 |-  res!=0. LOCS:[9;12;14;16] (must-bug)

 Is 7 due to the fact that we rely on input x?

*/

