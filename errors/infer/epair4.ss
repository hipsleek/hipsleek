data pair {
  int fst;
  int snd;
}


bool xZero0(int x)
  requires x<0
  ensures !res;
{
  x = x+1; //11:x'=x+1
  pair p = new pair(x,0);//{12}p'::pair<x',0>
  bool b = p!=null;//13: b'=p!=null
  x = x+1;//14 x'=x+1
  return b;//15 res=b'
}

/*
Post condition cannot be derived:
  path trace:    (must) cause:  res |-  !(res). LOCS:[9;13] (must-bug)

Why isn't 12 and 15 included?

  xpure[{12}:p'::Pair<..>] 
       ==> 12:p'!=null

Maybe we need <line,col> positioning for more
accurate identification of pre condition and statement.


*/

