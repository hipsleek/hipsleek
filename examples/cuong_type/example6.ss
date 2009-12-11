
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrU2[int]<p,P> == emp & p=self
			  or self::Elem[int]<v> * (self+1)::ArrU2[t]<p,P> * P<<self,v>> & p>self
		   	  mem (self,p-1,true);

ArrBag[int]<p,S> == emp & p=self & S = {}
			   or self::Elem[int]<v> * (self+1)::ArrBag[int]<p,S1> & S = union(S1,{v}) & p>self
			   mem (self,p-1,true);

func P4 == (\<S,i,v> i notin S or v > 0);

void part_init(int[] a, int[] b, int n)
	requires a::Arr[int]<a+n> * b::Arr[int]<b+n>
	ensures b::ArrBag[int]<b+n,S> * a::ArrU2[int]<a+n,(\<v> P4<<S,v>>)>;
{
	part_init_aux(a,b,n,0,0);
}

void part_init_aux(int[] a, int[] b, int c, int i, int j)
	requires (a+i)::Arr[int]<a+n> * (b+j)::Arr[int]<b+n>
	ensures (b+j)::ArrBag[int]<b+n,S> * (a+i)::ArrU2[int]<a+n,(\<v> P4<<S,v>>)>;
{
	if (i < n) {
	   if (a[i] > 0) {
	   	  b[j] = a+i;
		  part_init_aux(a,b,n,i+1,j+1);
	   }
	   else part_init_aux(a,b,n,i+1,j);
	}
}
