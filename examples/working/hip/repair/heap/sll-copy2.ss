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
      // return k;
  }
}


// synthesize [node x,node tmp,node k]
//  tmp::ll<n_7411> * k::node<Anon_7407,tmp>&
// x!=null & n_7411+1=n & n_7415=n_7411 & n_7414=n_7411 & flted_7_7406=n_7411
// ~>
//  (exists f_r_7427,f_r_7428: res::ll<f_r_7427>&
// Anon_7407=Anon_7407 & n_7411=flted_7_7406 & f_r_7427=flted_7_7406+1 & 
// f_r_7428=flted_7_7406+1 & flted_7_7406+1=f_r_7428).

// synthesize [node k,node tmp,node x]
//  tmp::ll<n_7458> * q_7455::ll<n_7458> * x::node<Anon_7454,q_7455> * 
//  k::node<Anon_7454,tmp>&
// flted_7_7453+1=n & !(v_bool_14_7433) & x!=null & x=x & n_7458=flted_7_7453 & 
// 0<=flted_7_7453
// ~>
//  (exists f_r_7480,f_r_7481: res::ll<f_r_7480> * x::ll<f_r_7481>&
// f_r_7480=flted_7_7453+1 & f_r_7481=flted_7_7453+1).
