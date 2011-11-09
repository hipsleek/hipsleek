data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

treelseg<t,p,d,h> == t::node<d,p> & self=null & h=0 
  or self::tree<left,right> * left::treelseg<t,r,d+1,h1> * right::treelseg<r,p,d+1,h2>
  & h = 1+max(h1,h2)
  inv h>=0;


bool is_empty(node x)
  case {
    x=null -> ensures res;
    x!=null -> ensures !res;
  }
{
	return x==null; 
}

int head(node x)
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

{
	if (is_empty(s)) {
		return null;
	}
	else {
		int h = head(s);
		if (h < d) {
			return null;
		}
		else if (h = d) {
			pop(s);
			return new tree(null, null);
		}
		else {
			tree l = build_rec(d+1, s);
			tree r = build_rec(d+1, s);
			return new tree(l, r);
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