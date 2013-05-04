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
  int y = p.fst; //14
  x = x+1;
  return y;
}

/*

 path trace:    (may) cause:  res=1+x |-  res!=0. LOCS:[7;9;12;14;16] (may-bug)

 Is 7 due to the fact that we rely on input x?

*/

