void loop(ref int x, ref int y)
//infer [@term] 
//infer [@post_n]
 case {
  x<=y -> requires Term[]  ensures x'<=y';
  x>y & x<0 -> requires Loop    ensures x'<=y';
  x>y & x>=0 -> requires MayLoop  ensures x'<=y';
 }
{ if (x>y) {
    y=x+y;
    x=x-1;
    loop(x,y);
  }
}

/*
sim2-loop.ss


*/
