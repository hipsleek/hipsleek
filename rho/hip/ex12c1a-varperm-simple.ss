  
void main()
  requires emp ensures emp;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  par 
    //{x,y@L,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     x = v+1;
    //dprint;
    || // {y@L,v@L}
  case {y@L,v@L} true ->
      y = y+22+v; // cannot update y
     //dprint;
  }
  dprint;
  assert x'=6 & y'=40+22+5;
}

/*
# ex12c1a.ss

  par 
    //{x,y@L,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     x = v+1;
    //dprint;
    || // {y@L,v@L}
  case {y@L,v@L} true ->
      y = y+22+v; // cannot update y
     //dprint;
  }

why did this fail?

Parsing file "ex12c1a-varperm-simple.ss" by default parser...
File "ex12c1a-varperm-simple.ss", line 12, characters 10-11
 --error: Stream.Error("CBRACE expected after [opt_cid_list] (in [excl_var_list])")
 at:caught


*/
