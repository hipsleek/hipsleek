/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
	inv n>=1 & sm<=lg;

bnd<n,sm:int,bg> ==
 		self=null & n=0
  or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d< bg 
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

relation A(bool x).
relation B(bool x).

lemma self::sll<n, sm, lg> -> self::ll<n>;

/*
NEW RELS: [ ( res<=0) -->  A(res), ( res<=0) -->  B(res), ( tmp_42' & A(tmp_42') & 1<=res) -->  A(res), ( !(tmp_42') & res<=0 & A(tmp_42')) -->  A(res), ( A(tmp_42') & 1<=res & tmp_42') -->  A(res), ( A(tmp_42') & res<=0 & !(tmp_42')) -->  A(res), ( A(tmp_42') & 1<=res) -->  A(res), ( res<=0) -->  B(res), ( 1<=res) -->  B(res), ( res<=0) -->  B(res), ( 1<=res) -->  B(res), ( res<=0) -->  B(res), ( B(tmp_42') & 1<=res & tmp_42') -->  B(res), ( B(tmp_42') & res<=0 & !(tmp_42')) -->  B(res), ( 1<=res) -->  B(res), ( 1<=res) -->  B(res), ( B(tmp_42') & 1<=res) -->  B(res)]
*/
// TODO: Use given specs to eliminate the unexpected branches while inferring B
bool bubble(node xs)
     infer [B]
     requires xs::ll<n> & xs!=null
     ensures xs::sll<n, s, l>  /*& A(res)*/  &!res
		or  xs::ll<n> & B(res);


{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {    
    //assume false;
		tmp = bubble(xs.next);
    int xv = xs.val;
    int xnv = xs.next.val;
		if (xv <= xnv) 
			flag = false;
		else {
			xs.val = xnv;
			xs.next.val = xv; //ERROR: lhs and rhs do not match
			flag = true; 
		}
		return (flag || tmp);	
	}
}

