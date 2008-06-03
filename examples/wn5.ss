
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

pd<x,y> == self::cell<x> & y=2x inv true;

void test(cell l)
 requires l::pd<x,y>
 ensures l::pd<x+1,y2>;
{
 int t;
 t=l.val;
 t=t+1;
 l.val = t;
}
void main()
{
 cell n=new cell(0);
 dprint;
 test(n);
 dprint;
 test(n);
 dprint;
 test(n);
 dprint;
}

