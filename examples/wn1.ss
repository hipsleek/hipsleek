
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

pair inc(pair x)
 requires x::pair<n,n>
 ensures res::pair<n+1,n>&res=x;
{
 dprint;
 int tmp = x.fst;
 tmp++;
 dprint;
 x.fst = tmp;
 dprint;
 return x;
}
