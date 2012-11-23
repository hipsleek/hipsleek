int bsearch(int a, int v, int low, int up)
case {
	low>up ->  variance [0,0] ensures "l1":true & res=-1 ;
	low<=up -> // variance up-low => low>up
               // bound -1 // should be a constant
			   variance [0,1,up-low]
               ensures "l2":true & (res=-1 | a=v & low<=res<=up);
			   /* case { */
			   /*  	a<v -> ensures "l2":true; */
			   /*  	a>v -> ensures "l3":true; */
			   /*  	a=v -> ensures	true; */
			   /*  } */
}
{
	if (low <= up) {
		int mid = low + (up-low)/2;
		int low1 = mid+1;
		int up1 = up;
		int low2 = low;
		int up2 = mid-1;
		if (lessthan(a,v)) {
			assert "l2":(up1'-low1')-(up'-low')<0;
			assert "l2":true & ((up1'-low1')>=0 | low1'>up1');
			assert "l2":(up1'-low1')>=-1 ;
			return bsearch(a,v,low1,up1);
		}
		else if (greaterthan(a,v)) {
			assert "l2":(up2'-low2')-(up'-low')<0;
			assert "l2":true & ((up2'-low2')>=0 | low2'>up2');
			assert "l2":(up2'-low2')>=-1;
			return bsearch(a,v,low2,up2);
		}
		else
			return mid;
	}
	else
		return -1;
}

bool lessthan(int a, int v)
requires true
//ensures a<v;
ensures res & a<v or !res & a>=v ;

bool greaterthan(int a, int v)
requires true
//ensures a>=v;
ensures res & a>v or !res & a<=v ;
