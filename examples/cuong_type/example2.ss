
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrBag[int]<p,S> == emp & p=self & S = {}
			   or self::Elem[int]<v> * (self+1)::ArrBag[int]<p,S1> & S = union(S1,{v}) & p>self
			   mem (self,p-1,true);

func P == (\<v> v!=0);

void copy_prop(int[] a, int[] b, int n)
	requires a::ArrBag[int]<a+n,B> * b::Arr[int]<b+n>
	ensures a::ArrBag[int]<a+n,B> * b::ArrBag[int]<b+n,B>;
{
	copy_prop_aux(a,b,n,0);
}

void copy_prop_aux(int[] a, int[] b, int n, int i)
	requires (a+i)::ArrBag[int]<a+n,B> * (b+i)::Arr[int]<b+n>
	ensures (a+i)::ArrBag[int]<a+n,B> * (b+i)::ArrBag[int]<b+n,B>;
{
	if (i < n) {
	   b[i] = a[i];
	   copy_prop_aux(a,b,n,i+1);
	}
}
