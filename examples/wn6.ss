
data cell { 
	int val; 
}

pd<x,y> == self::cell<x> & y=2x inv y=2x;

void test2(cell l)
 requires l::pd<a,b>
 ensures l::pd<a+1,b+2>;
/*
{
 int t;
 t=l.val;
 t=t+1;
 l.val = t;
 dprint;
}
*/

void main2()
{
 cell n=new cell(0);
 dprint;
 test2(n);
 dprint;
 test2(n);
 dprint;
}

