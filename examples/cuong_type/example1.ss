
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrU[int]<p,P> == emp & p=self
          or self::Elem[int]<v> * (self+1)::ArrU[int]<p,P> * P<<v>> & p>self
		  mem (self,p-1,true);

func P == (\<v> v!=0);

void copy_prop(int[] a, int[] b, int n)
	requires a::ArrU[int]<a+n,P> * b::Arr[int]<b+n>
	ensures a::ArrU[int]<a+n,P> * b::ArrU[int]<b+n,P>;
{
	copy_prop_aux(a,b,n,0);
}

void copy_prop_aux(int[] a, int[] b, int n, int i)
	requires (a+i)::ArrU[int]<a+n,P> * (b+i)::Arr[int]<b+n>
	ensures (a+i)::ArrU[int]<a+n,P> * (b+i)::ArrU[int]<b+n,P>;
{
	if (i < n) {
	   b[i] = a[i];
	   copy_prop_aux(a,b,n,i+1);
	}
}
