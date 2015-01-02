data node {
	int val;
	node next;
}

lseg<p, n> == self::node<_, p> & n = 1
	or self::node<_, r> * r::lseg<p, n-1>
	inv n >= 1;

s_lseg<p, n, sm, lg> == self::node<sm, p> & sm = lg & n = 1
	or self::node<sm, q> * q::s_lseg<p, n-1, qs, lg> & sm<=qs
	inv n >= 1 & sm <= lg;

equiv slseg_lseg(node x)
	requires x::s_lseg<p, n, _, _>
	ensures x::lseg<p, n>;
	requires x::lseg<p, n> 
	ensures x::s_lseg<p, n, _, _>;

bool bubble(node xs, node p)
	requires xs::lseg<p, n> //& n > 0
	ensures xs::s_lseg<p, n, s, l> & !res
		or  xs::lseg<p, n> & res;
{
	int aux, tmp1;
	bool tmp, flag; 

	assert xs' != null;
	assert xs'::node<_,_>;
	if (xs.next == p) {
		return false;
	}
	else {
		tmp = bubble(xs.next, p);
		if (xs.val <= xs.next.val) {
			flag = false;
		}
		else {
			aux = xs.val;
			tmp1 = xs.next.val;
			xs.val = tmp1;
			xs.val = xs.next.val; //ERROR: lhs and rhs do not match
			flag = true; 

			//if (!tmp) {
				//if (xs.next.next != null) { // this is the lemma step
					//--node tmp2 = xs.next.next;
					//--xs.next.next = id(tmp2);
					//id3(xs.next.next);
				//}
			//}
		}
		return (flag || tmp);	
	}
}





