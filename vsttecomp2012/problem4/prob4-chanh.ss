data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

treelseg<t,p,d,h> ==
     t::node<d,p> * self::tree<null, null> & h=1
  or self::tree<left,right> * left::treelseg<t,r,d+1,h1> * right::treelseg<r,p,d+1,h2>
     & h = 1+max(h1,h2)
  inv h>=1 & self!=null;

lseg<p, n> == self=p & n=0 
  or self::node<v, r> * r::lseg<p, n-1> //& v>0
  inv n>=0;

bool is_empty_lseg(node x)
  requires x::lseg<p, n>
  case {
    x=p -> ensures res;
    x!=p -> ensures !res;
  }
{
	return x==null; 
}

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
  //ensures x::node<i, _> * p::lseg<q, n> & res=i;
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

lemma "lsegbreakmerge" self::lseg<p, b+c> <-> self::lseg<q, b> * q::lseg<p, c>;

tree build_rec (int d, ref node s)

case {	
	s=null -> ensures res = null;
	s!= null -> 
	  
	requires s::lseg<p, _> //& s!= null //* p1::lseg<p,_>@I
	//ensures res::treelseg<s, s', d, _> * s'::lseg<p,_>;

	
	case { p=null ->
		ensures res::treelseg<s, s', d, _> * s'::lseg<p,_>;
	p!=null ->
	requires p::node<_,_>@I
		ensures res::treelseg<s, s', d, _> * s'::lseg<p,_>;
	}
	
	}

{
	
	if (s == null) {
		//assume false;
		return null;
	}
	else {
		//dprint;
		int h = hd(s);
		if (h < d) {
			assume false;
			return null;
		}
		else if (h == d) {
				   
			pop(s);
			dprint;
			//assume false;
			return new tree(null, null);
		}
		else {
			  assume false;
			tree lll = build_rec(d+1, s);
		//	assert s'=p1;
		//assert true;
		//dprint;
			tree rrr = build_rec(d+1, s);
	   //assume false;
		//assert true;
		//dprint;
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
