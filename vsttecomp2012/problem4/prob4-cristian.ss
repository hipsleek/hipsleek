data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

treell<t,p,d> == t::node<d,p> * self::tree<null, null>
  or self::tree<left,right> * left::treell<t,r,d+1> * right::treell<r,p,d+1> 
  inv true;

ll< n> == self=null & n=0 
  or self::node<v, r> * r::ll<n-1> 
  inv n>=0;

bool is_empty(node x)
  case {
    x=null -> ensures res;
    x!=null -> ensures !res;
  }
{
	return x==null; 
}

int hd(node x)
  requires x::node<i,_>@I
  ensures res=i;
{
	return x.val;
}

void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //' removes a node
{
	x = x.next;
}

tree build_rec (int d, ref node s)
case {	
	s=null -> ensures res = null;
	s!=null -> requires s::node<v, q>@I * q::ll<n>@I
		case {
			v<d ->  ensures res=null;
			v=d ->  ensures res::treell<s,s',d>@I & s'=q & 1>2;
			v>d ->  ensures res::treell<s, s', d>@I * s'::ll<n1>@I & n1<n;
		}	
	}
{
	if (is_empty(s)) {
		//assume false;
		return null;
	}
	else {
		int h = hd(s);
		if (h < d) {
		//	assume false;
			return null;
		}
		else if (h == d) {
			//assume false;
			pop(s);		
            dprint;
            assert false;
			return new tree(null, null); 
		}
		else {
			  assume false;
			tree lll = build_rec(d+1, s);
			tree rrr = build_rec(d+1, s);
			//dprint;
			assume false;
			return new tree(lll, rrr);
		}
	}
}



tree build(node s)
{
	tree t = build_rec(0, s);
	bool b = is_empty(s);
	if (!b) {
		return null;
	} else {
		return t;
	}
}
