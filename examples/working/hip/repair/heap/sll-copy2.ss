data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp = copy(x.next);
      node k = new node(x.val, tmp);
      return k.next;
  }
}


// synthesize [node x,node tmp,node k]
//  tmp::ll<n_7411> * k::node<Anon_7407,tmp>&
// x!=null & n_7411+1=n & n_7415=n_7411 & n_7414=n_7411 & flted_7_7406=n_7411
// ~>
//  (exists f_r_7427,f_r_7428: res::ll<f_r_7427>&
// Anon_7407=Anon_7407 & n_7411=flted_7_7406 & f_r_7427=flted_7_7406+1 & 
// f_r_7428=flted_7_7406+1 & flted_7_7406+1=f_r_7428).
