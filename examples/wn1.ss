
data cell { 
	int val; 
}

data pair { 
	int fst; 
	int snd; 
}

cell inc(cell x)
 requires x::cell<n>
 ensures res::cell<n+1>&res=x;
{
 dprint;
 int tmp = x.val;
 tmp++;
 dprint;
 x.val = tmp;
 dprint;
 return x;
}
