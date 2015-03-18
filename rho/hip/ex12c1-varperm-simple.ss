  
void main()
  requires true ensures true;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  par 
    {x,y@L,v@L}
  {  
   // exists r1',r2'
  case {x,v@L} true ->
     //dprint;
     x = v+1;
     //dprint;
    || // {y@L,v@L}
  else // {y@L,v@L} 
      ->
      //int y;
      //y = y+22+v; // cannot update y
      dprint;
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
  else // {y@L,v@L}   end?
      ->
      y = y+22+v; // cannot update y
     //dprint;
  }

Problems:
 (i) What happen to varperm?
 (ii) Why did we not have a *-combine at the end

 State:htrue&x_36'=1+v_38'&{FLOW,(4,5)=__norm#E}[]

 ]

dprint: ex12c1-varperm-simple.ss:19: ctx:  List of Failesc Context: [FEC(0, 0, 1
  [])]

Successful States:
[
 Label: []
 State:emp&y_37'=v_38'+22+y_1373 & v_38'=5 & y_1373=40 & x_36'=4&{FLOW,(4,5)=__n
orm#E}[]

# There seems to be a combine error below..

 State:emp&{FLOW,(4,5)=__norm#E}[]



*/
