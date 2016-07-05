data node {
	int val;
	node next;
}

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;


//andreeac: infers v2<=0, what about v1? thought it infers v2<=0, in !!! NEW SPECS it says .......... p::node<v,flted_21_34>@L .........
void append(node x, node y)
  infer [v1, v2] // infer [v1] infers nothing. is it correct?
  requires x::lseg<p,n>@v1 *  p::node<v,null>@v2 
  ensures p::node<v,y>;
{
        //dprint;
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		dprint; 
		append(x.next, y); 
		return;
	}
	else {
                //dprint;
		x.next = y;
		return;
	}
}
