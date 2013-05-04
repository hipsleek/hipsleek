data pair {
  int fst;
  int snd;
}


int xZero0(int x)
  requires x<0
  ensures res!=0;
{

  x = x+1; //12
  pair p = new pair(x,0);
  int y = p.fst; //14
  x = x+1;
  return y;
}

/*

  path trace:    (may) cause:  x<0 & res=1+x |-  res!=0. 
        LOCS:[7;8;9;12;14;16] 
  13 is not captured, which may be an issue since it is build 
  from an intermediate data structure. Is this important though?

*/

