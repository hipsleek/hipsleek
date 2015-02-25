  
void main()
  requires emp ensures emp;
{
  int x,y,v;
  x=4; y=40; v=5
  dprint;
  par {x,y,v}
  {  
   // exists r1',r2'
  case {x,v@0.5} true ->
     x = v+1;
    //dprint;
    || // {y,v@0.5}
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
