//To test phase inference with mutual recursive calls
//Need to declare p1, p2, p3, p4 as logical variables 

logical int p1, p2, p3, p4;

void f (int x, int y)
/*
infer [p1,p2,p3,p4,y]
case {
	y>=0 -> requires Term[p1,y] ensures true;
	y<0 -> requires Term[p2] ensures true;
}
*/

case {
	y>=0 -> requires Term[y] ensures true;
	y<0 -> requires Term[] ensures true;
}

/*
case {
	y>=0 -> requires Term[1,y] ensures true;
	y<0 -> requires Term[1] ensures true;
}
*/
{
	if (y>=0) {
		f(x, y-1);
	}
 	else {
		g(x, y);
	}
}

void g (int x, int y)
/*
infer [p1,p2,p3,p4] 
case {
	y>=0 -> requires Term[p3] ensures true;
	y<0 -> requires Term[p4,x] ensures true;
}
*/

case {
	y>=0 -> requires Term[] ensures true;
	y<0 -> requires Term[x] ensures true;
}

/*
case {
	y>=0 -> requires Term[2] ensures true;
	y<0 -> requires Term[0,x] ensures true;
}
*/
{
	if (y>=0) {
		f(x, y);
	} 
	else {
		g(x+y, y);
	}
}
