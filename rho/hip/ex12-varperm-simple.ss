  
void main()
  requires emp ensures emp;
{
  int x,y;
  x=4; y=40;
  dprint;
  par {x,y}
  {  
   // exists r1',r2'
  case {x} true ->
     x = x+1;
    dprint;
  || 
    else  -> // y@M
     y = y+22;
   dprint;
  }
  dprint;
}

/*
# ex4a.ss

      x = new cell(1); 
      y = new cell(2); 
      dprint;
      countDown(c);
      dprint;
      int k = x.val;

How come no printing?
How come can still access x.val?

What is:
       EXISTS(v_int_47_1431': c_42'::LatchIn<> * c_42'::LatchOut<> * c_42'::CNT<v_int_47_1431'>&v_int_47_1431'=1)[]


Successful States:
[
 Label: []
 State:(exists v_int_47_1431': c_42'::LatchIn{ - (exists flted_47_1581,flted_47_1582: x_40'::cell<flted_47_1582> * 
y_41'::cell<flted_47_1581>&flted_47_1582=1 & flted_47_1581=2&
{FLOW,(4,5)=__norm#E})[]}<> * c_42'::LatchOut{ + (exists flted_47_1583,flted_47_1584: x_40'::cell<flted_47_1584> * 
y_41'::cell<flted_47_1583>&flted_47_1584=1 & flted_47_1583=2&
{FLOW,(4,5)=__norm#E})[]}<> * c_42'::CNT{}<v_int_47_1431'>&v_int_47_1431'=1&{FLOW,(4,5)=__norm#E})[]
       EXISTS(v_int_47_1431': c_42'::LatchIn<> * c_42'::LatchOut<> * c_42'::CNT<v_int_47_1431'>&v_int_47_1431'=1)[]

 ]


*/
