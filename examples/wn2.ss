
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

pair inc(pair x)
 requires x::pair<n,_>
 ensures res::pair<n+1,_>&res=x;
{
 dprint;
 int tmp = x.fst;
 tmp++;
 //dprint;
 x.fst = tmp;
 //dprint;
 return x;
}

pair twice(pair x)
 requires x::pair<n,n>
 ensures res::pair<n+2,_>&res=x;
{
 dprint;
 pair tmp = inc(x);
 dprint;
 tmp = inc(x);
 dprint;
 return tmp;
}
