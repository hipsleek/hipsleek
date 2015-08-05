void loop(int x, int tx) 

 case {
   ((tx<x & 0<=x) | x<=(0-1)) -> 
       requires emp & Term[69,1]
       ensures emp & true;
   0<=x & x<=tx -> 
     requires emp & Term[69,2,0+(0*x)+(1*tx)]
     ensures emp & true;
   
 }
{
  if (x>=0 && x <= tx) {
    tx = x - 1;
    x = __VERIFIER_nondet_int();
    //infer_assume [x];
    loop(x, tx);
  }
}
