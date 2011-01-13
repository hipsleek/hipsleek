int bsearch(int a, int v, int low, int up)
case {
	low>up ->  ensures "l1":true & res=-1 ;
	low<=up -> variance (1) [up-low]
               ensures "l2":true & (res=-1 | a=v & low<=res<=up);
}
{
	if (low <= up) {
		int mid = low + (up-low)/2;
		int low1 = mid+1;
		int up1 = up;
		int low2 = low;
		int up2 = mid-1;
		if (lessthan(a,v)) {
			return bsearch(a,v,low1,up1);
		}
		else if (greaterthan(a,v)) {
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
