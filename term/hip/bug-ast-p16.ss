logical int p1,p2,p3,p4;

// TODO : wrong translation!!
//EBase: [][]Term LexVar[[1,0-x-4]] FLOW __norm) {
//x<1 -> EBase true & Term[0,1,0 - (x - 4)] &
 
void loop (int x, int y)
  infer [p1,p2,p3,p4]
case {
  x <= y -> requires Term[0] ensures true;
  x > y -> case {
    x>1 -> requires Term[0,x-y] ensures true;
	x=1 -> requires Term[1] ensures true;
	x<1 -> requires Term[1,-x-4] ensures true;
 }
}
{
	if (x > y) {
		loop(x+1, x+y);
	} 

}
