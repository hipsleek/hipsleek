
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

pair inc(pair x)
 requires x::pair<n,m>
 ensures res::pair<n+1,m>&res=x;
{
 //dprint;
 int tmp = x.fst;
 tmp++;
 //dprint;
 x.fst = tmp;
 //dprint;
 return x;
}

pair twice(pair x)
 requires x::pair<n,n>
 ensures res::pair<n+2,n>&res=x;
{
 dprint;
 pair tmp = inc(x);
 dprint;
 tmp = inc(x);
 dprint;
 return tmp;
}
