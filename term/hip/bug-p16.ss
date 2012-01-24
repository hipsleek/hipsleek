logical int p1,p2,p3,p4;

void loop (int x, int y)
  infer [p1,p2,p3,p4]
case {
  x <= y -> requires Term[0] ensures true;
  x > y -> case {
    x>1 -> requires Term[0,x-y] ensures true;
	//x=1 -> requires Term[1] ensures true;
	x<=1 -> requires Term[1,-x+1] ensures true;
 }
}
{
	if (x > y) {
		loop(x+1, x+y);
	} 

}

/*
TODO : why is there a transition for boundedness checking?

Termination checking result:
(10)->(15) (ERR: not bounded) 
*/
