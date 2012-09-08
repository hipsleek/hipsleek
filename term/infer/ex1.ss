int loop (int x)

requires true
ensures true;

/*
requires x>=0
case {
	x=0 -> ensures true;
	x>0 -> ensures true;
	x<0 -> ensures false; //Unreachable from pre-condition
}
*/
{
	int r;
	if (x==0) {
		//dprint;
		r = 0;
	} else {
		//dprint;
		//if (x>2)	
			r = loop(x-2);	
			//if (x<5) loop(x-2);
			//else loop(x-1);
			
		//else r = loop(x+1);
		return r;
	} 
	return r;
}

/*
{
	//int r = loop(x-1);
	return 0;
}
*/
/*
{
	int r;
	if (x==0) r = 0;
	else if (x>0) {
		r = loop(x-1); 
		if (x<0) loop(x+1);
		else r = 0;
		return r;
	} else r = loop(x+1);
	return r;
}
*/
