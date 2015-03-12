/* bubble sort */

data node [b]{
	b val;
	node[b] next;
}

//------------------------------------------------------------------------------------------
// views
//------------------------------------------------------------------------------------------

ho_pred ll_shape[t,b]<a:t>[Base,Rec]
  == Base(a,self)
      or self::node[b]<v,q>* q::ll_shape[t,b]<aq>* Rec(a,aq,self,v,q)
      inv Inv(a,self);

ho_pred ll_Base[t,b]<a:t>[Base,Rec] refines ll_shape[t,b]<a>
  with 
    {
      Base(a,self) = self=null
    }
      
ho_pred ll_S[set[b],b]<S:set[b]>[Base,Rec] extends ll_Base [set[b],b]<S>
  with { Base(S,_) = S={} 
         Rec(S,Sq,self,v,p,q) = S=union(Sq,{v})
       }

ho_pred sll [set[b],b]<S:set[b]>[Base,Rec] refines ll_S [set[b],b]<S>
  with {  
         Rec(S,Sq,self,v,p,q) = forall(x: (x notin Sq | v <= x))
       }
       
ll1<S> == finalizes ll_S[int]<>;
sll1<S> == finalizes sll[int]<>;


/*
ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));
*/
//insert to last
void id1(node x)
	requires x::sll1<S> & S != {}
	ensures x::ll1<S>;
{
	if (x.next != null) {
		id1(x.next);
	}
}

//------------------------------------------------------------------------------------------
// bubble function
//------------------------------------------------------------------------------------------
bool bubble1(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S> & !res
		or  xs::ll1<S> & res ;
{
	int aux;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {
		flag = false;
		tmp = bubble1(xs.next);
		if (xs.val > xs.next.val) {
			aux = xs.val;
			xs.val = xs.next.val;
			xs.next.val = aux; //swap(xs);
			flag = true; 

			if (!tmp) {
				if (xs.next.next != null) { // this is the lemma step
					id1(xs.next.next);
				}
			}
		}
		return (flag || tmp);	
	}
}


//------------------------------------------------------------------------------------------
// bsort function
//------------------------------------------------------------------------------------------

void bsort1(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
{
	bool b;

	b = bubble1(xs);
	if (b) {
		bsort1(xs);
	}
}

