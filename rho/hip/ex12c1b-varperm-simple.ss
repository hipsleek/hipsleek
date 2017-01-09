  
void main()
  requires emp ensures emp;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  par 
    {x,y,v@L} // rem {v}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     //dprint;
     x = x + v + 1; // cannot read v
     //dprint;
  || // {y,v@L}
  else // {y,v@L} 
      ->
      //int y;
      //dprint;
      y = y+22+v; // cannot update y
      //dprint; 
  }
  dprint;
  assert x'=10; //& y'=40+22+5;
  v = v + 1;
  y = y + 33;
  dprint;
  assert v'=6 & y' = 40+22+5+32; //failed
}
