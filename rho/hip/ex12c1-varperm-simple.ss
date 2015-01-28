  
void main()
  requires emp ensures emp;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  par 
    {x,y@L,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     x = v+1;
    //dprint;
    || // {y@L,v@L}
  else // {y@L,v@L} 
      ->
      y = y+22+v; // cannot update y
     //dprint;
  }
  dprint;
  assert x'=6 & y'=40+22+5;
}

/*
# ex12c1.ss

  par 
    {x,y@L,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     x = v+1;
    //dprint;
    || // {y@L,v@L}
  else // {y@L,v@L} 
      ->
      y = y+22+v; // cannot update y
     //dprint;
  }
Why parser error?

File "ex12c1-varperm-simple.ss", line 9, characters 4-5
 --error: Stream.Error("[par_case_list] expected after OBRACE (in [par_statement])")
 at:caught

Exception occurred: Stream.Error("[par_case_list] expected after OBRACE (in [par_statement])")

*/
