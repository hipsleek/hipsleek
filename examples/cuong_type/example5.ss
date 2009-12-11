
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrU[int]<p,P> == emp & p=self
		  or self::Elem[int]<v> * (self+1)::ArrU[int]<p,P> * P<<v>> & p>self
		  mem (self,p-1,true);

func P3 == (\<v> v=0);

void partition(int[] a, int[] b, int[] c, int n)
	requires a::Arr[int]<a+n> * b::Arr[int]<b+n> * c::Arr[int]<c+n>
	ensures a::Arr[int]<a+n> * b::ArrU[int]<b+n1,P3> * c::ArrU[int]<c+n-n1,(\<v> v!=0)>;
{
	partition_aux(a,b,c,n,0,0,0);
}

void parition_aux(int[] a, int[] b, int[] c, int n, int i, int j, int k)
	requires (a+i)::Arr[int]<a+n> * (b+j)::Arr[int]<b+n> * (c+k)::Arr[int]<c+n>
	ensures (a+i)::Arr[int]<a+n> * (b+j)::ArrU[int]<b+n1,P3> * (c+k)::ArrU[int]<c+n-n1,(\<v> v!=0)>;
{
	if (i<n) {
	   if (a[i] = 0) {
	   	  b[j] = 0;
		  partition_aux(a,b,c,n,i+1,j+1,k);
	   }
	   else {
	   	  c[k] = a[i];
		  partition_aux(a,b,c,n,i+1,j,k+1);
	   }
	}
}
