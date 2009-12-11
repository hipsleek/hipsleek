
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

ArrA[int]<p,R,f,l> == self::Elem[int]<f> & p=self+1 & f=l
			  	 or self::Elem[int]<f> * (self+1)::ArrA[int]<p,R,f1,l> * R<<f,f1>> & p>self+1
			  	 mem (self,p-1,true);

func R == (\<u,v> u <= v);

void insert(int[] a, int v, int n)
	requires a::ArrA[int]<a+n,R,_,_> * (a+n)::Elem[int]<_>
	ensures a::ArrA[int]<a+n+1,R,_,_>;
{
	insert_aux(a,v,n,n);
}

void insert_aux(int[] a, int v, int i, int n)
	requires a::ArrA[int]<a+i,R,_,_> * (a+i)::Elem[int]<_> * (a+i+1)::ArrA[int]<a+n+1,R,_,_>
	ensures a::ArrA[int]<a+i,R,_,_> * (a+i)::ArrA[int]<a+n+1,R,_,_>;
{
	if (i>0) {
	   if (a[i-1] > v) {
	   	  a[i] = a[i-1];
		  insert_aux(a,v,i-1,n);
	   }
	   else {
	   	  a[i] = v;
	   }
	}
}
