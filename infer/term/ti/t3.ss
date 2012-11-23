// ANY-DOWN in Transition Invariant paper
// fair termination issues here

void loop0(ref int y, ref int x)
 case {
  x=1 -> requires Loop ensures false;
  x!=1 -> requires Term[] ensures true;
 }
{
  if (x==1) {
    y = y+1;
    loop0(y,x);
  }
}

void loop2(ref int y)
 case {
   y<=0 -> requires Term[] ensures y'=y; //'
   y>0 -> requires Term[y] ensures y'=0; //'
 }
{
  if (y>0) {
    y=y-1;
    loop2(y);
  }
}

/*

  loop0(y,x);loop1(y) || x=0  


*/
