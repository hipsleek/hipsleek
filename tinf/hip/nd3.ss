
/*
void loop()
 requires Loop
  ensures false;
*/

int non_det()
 requires true & Term[]
 ensures true;


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

/*
# nd3.ss

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
