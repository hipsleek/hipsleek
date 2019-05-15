/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> & n > 0;

node2 copy(node2 x)
requires x::dll<p, n>
ensures x::dll<p, n> * res::dll<p, n>;
{
  if (x == null) return x;
  else {
      node2 tmp = copy(x.next);
      node2 tmp2 = x.prev;
      node2 tmp3 = new node2(x.val, tmp2, tmp);
      if (tmp != null) tmp.prev = tmp3;
      dprint;
      return tmp3;
  }
}

// looping

// synthesize [node2 x,node2 tmp,node2 tmp2,node2 tmp3]

// tmp3::node2<Anon_15492,tmp2,tmp> * x::node2<Anon_15492,p,q_15493> *
//  q_15493::dll<p_15496,n_15497> * tmp::dll<p_15496,n_15497>&
// !(v_bool_23_15464) & n_15503=n_15497 & p_15502=p_15496 & n_15501=n_15497 & 
// p_15500=p_15496 & x=p_15496 & self_15490=p_15496 & p_15489=p & 
// flted_12_15491=n_15497 & x=p_15496 & tmp2=p & n_15497+1=n & 0<n & 
// p_15496!=null & tmp=null
// ~>
//  (exists f_r_15555,
// f_r_15556: res::dll<tmp2,f_r_15555> * x::dll<tmp2,f_r_15556>&
// f_r_15555=flted_12_15491+1 & f_r_15556=flted_12_15491+1)