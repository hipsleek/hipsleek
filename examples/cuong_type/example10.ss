
data node {
	 int val;
	 node prev;
	 node next;
}

ll<n,pr,P> == self = null & pr = null & n = 0
		   or P<<self,pr,q>> * q::ll<n-1,self,P>
		   inv n >= 0;

func F1 == (\<v,pr,nx> v::node<_,null,nx>);

func F2 == (\<v,pr,nx> v::node<_,pr,nx>);
