//Phase-change example
//VMCAI04 - A complete method for the synthesis of linear ranking functions

logical int p0, p1, p2, p3, p4;

void phase (ref int x)

infer[p0,p1,p2,p3,p4]
case {
  x<0 -> requires Term[p0] ensures x'<0;
  x>5 -> requires Term[p1] ensures x'<0;
  0<=x<=2 -> requires Term[p2] ensures x'<0;
  4<=x<=5 -> requires Term[p3] ensures x'<0;
  2<x<=3 -> requires Term[p4] ensures x'<0;
}
{
	if (x>=0) {
		x = 10-2*x;
   	phase (x);
 	}
	//else return;
}
