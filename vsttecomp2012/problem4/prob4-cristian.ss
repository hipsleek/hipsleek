data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

treelseg<t,p,d,h> == t::node<d,p> * self::tree<null, null> & h=1
  or self::tree<left,right> * left::treelseg<t,r,d+1,h1> * right::treelseg<r,p,d+1,h2> & h = 1+max(h1,h2)
  inv h>=0;

lseg<p, n> == self=p & n=0 
  or self::node<v, r> * r::lseg<p, n-1> & v>0
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

coercion "lsegbreakmerge" self::lseg<p, b+c> <-> self::lseg<q, b> * q::lseg<p, c>;

tree build_rec (int d, ref node s)
case {	
	s=null -> ensures res = null;
	s!=null -> requires s::node<v, q> * q::lseg<p,l>
		case {
			v<d ->  ensures res=null;
			v=d ->  ensures res::treelseg<s,s',d,1> * q::lseg<p,l> & s'=q;
			v>d ->  ensures res::treelseg<s', s', d, _> * s'::lseg<p,l1> & l1<l;
		}	
	}
{
	if (is_empty(s)) {
		assume false;
		return null;
	}
	else {
		int h = hd(s);
		if (h < d) {
			assume false;
			return null;
		}
		else if (h == d) {
			assume false;
			pop(s);
			return new tree(null, null); 
		}
		else {
			//  assume false;
			tree lll = build_rec(d+1, s);
			tree rrr = build_rec(d+1, s);
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
