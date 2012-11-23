//Phase-change example
//VMCAI04 - A complete method for the synthesis of linear ranking functions

void phase (ref int x)
case {
  x<0 -> requires Term[0] ensures x'<0;
  x>5 -> requires Term[1] ensures x'<0;
  0<=x<=2 -> requires Term[2] ensures x'<0;
  4<=x<=5 -> requires Term[3] ensures x'<0;
  2<x<=3 -> requires Term[4] ensures x'<0;
}
{
	if (x>=0) {
		x = 10-2*x;
   	phase (x);
 	}
	//else return;
}
