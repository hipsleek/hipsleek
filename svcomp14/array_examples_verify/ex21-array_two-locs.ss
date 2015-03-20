// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x)
  infer[@post_n]
  requires true
//ensures res=x+1;
  ensures true;
{
  int[] a;
  //int i =5;
  a[5] = x+1;
  a[6] = 2;
  int r;
  r = a[5]+a[6];
  return r;

}

/*
  forall (x: A & B)
  ==> forall(x:A) & B
  
   (a[5]=5 & i=j)-> i=j ->res & a[5]=5

forall i (non-trial ^ a[i]=5) -> forall i (a[i]=5)
forall i (non_trial) -> non-ti

     B --s--> B'
 ---------------------------------------
  forall (i: A & B) --s--> forall(i:A & B')


  forall(i:A & B) --> forall(i:A) & B

*/
