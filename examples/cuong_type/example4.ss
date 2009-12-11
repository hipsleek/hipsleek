
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrBag[int]<p,S> == emp & p=self & S = {}
			   or self::Elem[int]<v> * (self+1)::ArrBag[int]<p,S1> & S = union(S1,{v}) & p>self
			   mem (self,p-1,true);

func P2 == (\<v,w> v!=w);

int find(int[] a, int n, int v)
	requires a::Arr[int]<a+n>
	ensures a::ArrBag[int]<a+n,B> & res=-1 & forall (w: (w notin B | v != w))
			or a::Arr[int]<a+n> & res != -1;
{
	find_aux(a,n,0,v);
}

int find_aux(int[] a, int n, int i, int v)
	requires (a+i)::Arr<a+n>
	ensures (a+i)::ArrBag[int]<a+n,B> & res=-1 & forall (w: (w notin B | v != w))
			or (a+i)::Arr[int]<a+n> & res!=-1;
{
	if (i<n)
	{
		if (v = a[i]) return i;
		find_aux(a,n,i+1,v);
	}
	else return -1;
}
