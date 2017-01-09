
/*
void loop()
 requires Loop
  ensures false;
*/

int non_det()
 requires true & Term[]
 ensures true;

global int non_det_val;

void loop(int x, int y, int k)
 infer [@term]
 case {
  k<1 ->  requires Term[] ensures true & flow __Exc;
  k>=1 -> requires Term[x] ensures true & flow __norm;
 }
{
  if (x>=0) {
    x = x-y;
    y = k;
    if (y<1) raise new __Exc();
     loop(x, y);
 }
}

/*
# nd5a.ss

void loop(int x, int y)
 infer [@term]
 requires true
 ensures true;
{
  int k = non_det();
  if (x>=0 
      && (k>0)) {
    x = x + y;
    loop(x, y);
 }
}

I got below. Is it correct?
It uses MayLoop rather than Loop

Termination Inference Result:
loop:  case {
  x<=(0-1) -> requires emp & Term[72,1]
     ensures emp & true; 
  0<=x -> requires emp & MayLoop[]
     ensures emp & true; 
  }


*/
