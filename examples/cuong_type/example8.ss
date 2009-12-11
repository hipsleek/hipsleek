
Elem[int]<u> == self::int<u> 
			mem (self,self,true);

Arr[int]<p> == emp & p=self
		  or self::Elem[int]<_> * (self+1)::Arr[int]<p> & p>self
	   	  mem (self,p-1,true);

ArrA[int]<p,R,f,l> == self::Elem[int]<f> & p=self+1 & f=l
			  	 or self::Elem[int]<f> * (self+1)::ArrA[int]<p,R,f1,l> * R<<f,f1>> & p>self+1
			  	 mem (self,p-1,true);

func R == (\<u,v> u <= v);

void sort(int[] a, int n)
	requires a::Arr[int]<a+n>
	ensures a::ArrA[int]<a+n,R,_,_>;
{
	loop1(a,n,1);
}

void loop1(int[] a, int n, int i)
	requires a::ArrA[int]<a+i,R,_,_> * (a+i)::Arr[int]<a+n>
	ensures a::ArrA[int]<a+n,R,_,_>;
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
