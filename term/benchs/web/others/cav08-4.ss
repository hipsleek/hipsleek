/********************************************************
Example from 
	"Proving Conditional Termination", Byron Cook et al. (CAV'08)
	"A complete method for the synthesis of linear ranking functions", Rybalchenko et al. (VMCAI'04)
*********************************************************/

void loop (ref int x)
case {
  x<0 -> requires Term ensures x'<0;
  x>5 -> requires Term ensures x'<0;
  0<=x<=2 -> requires Term ensures x'<0;
  4<=x<=5 -> requires Term ensures x'<0;
  2<x<=3 -> requires Term ensures x'<0;
}
{
	if (x>=0) {
		x = 10-2*x;
   	loop (x);
 	}
	//else return;
}
