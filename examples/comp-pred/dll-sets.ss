/* doubly linked lists */

/* representation of a node */
data node2[b] {
	b val; 
	node2[b] prev;
	node2[b] next;	
}

/* view for a doubly linked list with bag of values */

ho_pred dll_shape[t,b]<a:t>[Base,Rec]
  == Base(a,self)
      or self::node2[b]<v,p,q>* q::dll_shape[t,b]<aq>* Rec(a,aq,self,v,p,q)
      inv Inv(a,self);
       
ho_pred dll_PBase[node2[b],b]<a:node2[b]>[Base,Rec] extends dll_shape[node2[b],b]<a>
      with { 
            Base(a,_) = self = null  
            Rec(a,aq,self,v,p,q) = a = p & self = aq
           }
      
ho_pred dll_S[b]<S:set[b]>[Base,Rec] extends dll_PBase[set[b],b]<S>
      with { Base(S,_) = S={} 
             Rec(S,Sq,v,...) = S = union(Sq, {v})
      }
      
dll1<p,S> == finalizes dll_S[int]<S> split dll_PBase[int]<p>;
  
/*dll1<p,S> == self = null & S = {} 
	or self::node2<v ,p , q> * q::dll1<q1, S1> & S = union(S1, {v}) & self = q1; 
*/
void insert(node2 x, int a)
	requires x::dll1<p, S> & S != {} 
	ensures x::dll1<p, S1> & S1 = union(S, {a}); 
{
	node2 tmp_null = null;

		if (x.next == null) {
			x.next = new node2(a, x, tmp_null);
		}
		else {
			insert(x.next, a);
		}
}


node2 append(node2 x, node2 y) // for this I got the Mona + Isabelle timings
	requires x::dll1<q, S1> * y::dll1<p, S2>
	ensures res::dll1<_, S> & S = union(S1, S2);
{
	node2 tmp;

	if (x == null)
		return y;
	else
	{ 	

		//tmp = x.next;
		tmp = append(x.next, y);

		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}

		return x; 
	}
}
