
void loop(ref int x) 
 case {
  x>11 ->  requires xx=1 & x>=0 ensures  xx>=1 & x'=10; //'
   x<=11 ->  requires [xx] xx=0 ensures x'=x-1 ; //'
  }
{
  int z=x;
  x=x-1;
  dprint;
  if (x>10) {
    assert x-x'>0 & x'>=0;
    assert z'-x'>1; 
    assert xx=1;
    
    loop(x);
  }
}


void inc(ref int x)
requires true ensures x'=x+2;
{
 //{x,x'}
 dprint;
 {int y;
   // {x,x',y,y'}
   x=x+1;
   y=x+1;
   dprint;
   {int y;  //possible translation issue
     // {x,x',y,y'}
     x=x+1;
     y=x+1;
     dprint;
   };
 };

 //{x,x'}
 dprint;
}




