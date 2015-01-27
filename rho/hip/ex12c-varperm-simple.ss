  
void main()
  requires emp ensures emp;
{
  int x,y,v;
  x=4; y=40; v=5
  dprint;
  par {x,y,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     x = v+1;
    //dprint;
    || // {y,v@L}
    else  ->
     y = y+22+v;
     //dprint;
  }
  dprint;
  assert x'=6 & y'=40+22+5;
}

/*
# ex4a.ss


*/
