
/*
void loop()
 requires Loop
  ensures false;
*/

int non_det()
 requires true & Term[]
 ensures true;

global int k_non_det;

void loop(int x, int y)
 infer [@term]
 requires true
 ensures true;
{
  int k = k_non_det; //non_det();
  if (x>=0 
      && (k>0)) {
    x = x + y;
    loop(x, y);
 }
}

/*
# nd4.ss

Termination Inference Result:
loop:  case {
  ((k_non_det_16<=0 & 0<=x) | x<=(0-
  1)) -> requires emp & Term[71,1]
     ensures emp & true; 
  1<=k_non_det_16 & 
  0<=x -> case {
           0<=y -> requires emp & Loop[]
     ensures false & false; 
           y<=(0-1) -> requires emp & Term[71,2,0+(1*x)+(0*y)+(0*
           k_non_det_16)]
     ensures emp & true; 
           }
  
  }

Above shows that definite loop is reachable
Is it sound?


*/
