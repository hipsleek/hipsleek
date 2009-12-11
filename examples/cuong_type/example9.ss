
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrA[int]<p,R,f,l> == self::Elem[int]<f> & p=self+1 & f=l
			  	 or self::Elem[int]<f> * (self+1)::ArrA[int]<p,R,f1,l> * R<<f,f1>> & p>self+1
			  	 mem (self,p-1,true);

ArrBag[int]<p,S> == emp & p=self & S = {}
			   or self::Elem[int]<v> * (self+1)::ArrBag[int]<p,S1> & S = union(S1,{v}) & p>self
			   mem (self,p-1,true);

func R == (\<u,v> u <= v);

void sort(int[] a, int n)
	requires a::Arr[int]<a+n>
	ensures a::ArrA[int]<a+n,R,_,_>;
	requires a::ArrBag[int]<a+n,B>
	ensures a::ArrBag[int]<a+n,B>;
{
	loop1(a,n,1);
}

void loop1(int[] a, int n, int i)
	requires a::ArrA[int]<a+i,R,_,_> * (a+i)::Arr[int]<a+n>
	ensures a::ArrA[int]<a+n,R,_,_>;
	requires a::ArrBag[int]<a+i,B1> * (a+i)::ArrBag[int]<a+n,B2>
	ensures a::ArrBag[int]<a+n,B> & B = union(B1,B2);
{
	if (i < n) {
	   j = i;
	   loop2(a,n,j);
	   loop1(a,n,i+1);
	}
}

void loop2(int[] a, int n, int j)
	requires a::ArrA[int]<a+j,R,_,_> * (a+j)::Arr[int]<a+n>
	ensures a::ArrA[int]<a+j+1,R,_,_> * (a+j+1)::Arr[int]<a+n>;
	requires a::ArrBag[int]<a+j,B1> * (a+j)::ArrBag[int]<a+n,B2>
	ensures a::ArrBag[int]<a+j+1,B3> * (a+j+1)::ArrBag[int]<a+n,B4> & union(B1,B2) = union(B3,B4);
{
	int t;
	if (j > 0) {
	   k = j-1;
	   if (a[j] < a[k]) {
	   	  t = a[j];
		  a[j] = a[k];
		  a[k] = t;
		  loop2(a,n,j-1);
	   }
	}
}
