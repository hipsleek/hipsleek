/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm> ==
		self::node<sm, null> &  n=1 
	or	self::node<sm, q> * q::sll<n-1, qs> & q!=null & sm<=qs 
	inv n>=1 ;

bnd<n,sm:int,bg> ==
 		self=null & n=0
  or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d< bg 
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

//lemma self::sll<n, sm, lg> <- self::ll<n>;


/*
lls<n,k,sm> == self=null & n=0 & k=0 & sm=\inf
  or self::node<v, r> * r::lls<n-1,k,sm> & n>k & v<=sm
  or self::node<sm, r> * r::lls<n-1,k-1,sm1> & n=k & sm<=sm1
	inv n>=k & k>=0;
*/

lls<n,k,sm> == case {
    n=k -> [] self=null & n=0  & sm=\inf 
         or self::node<sm,r>*r::lls<n-1,k-1,sm1> & sm<=sm1;
    n!=k -> [] self::node<v, r> * r::lls<n-1,k,sm> & n>k & v<=sm;
}	inv n>=k & k>=0;

lemma self::sll<n, sm> -> self::lls<n,n,sm>;


bool bubble(node xs)
/*
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
		or  xs::ll<n> & res;
*/
  requires xs::lls<n,k,sm> & n>0  & Term[n]
  case {
    k=n -> ensures xs::sll<n,sm> & !res;
    k!=n -> ensures xs::sll<n, s> & !res & s<=sm
              or  xs::lls<n,k1,sm1> & res & k1=k+1 & sm1<=sm;
  }
{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
          //assume false;
          return false;
	}
	else {
          tmp = bubble(xs.next);
          int xv = xs.val;
          int xnv = xs.next.val;
          if (xv <= xnv) {
            //assume false;
            flag = false;
          }
          else {
            xs.val = xnv;
            xs.next.val = xv; //ERROR: lhs and rhs do not match
            flag = true; 
            //dprint;
            //assume false;
          }
          return (flag || tmp);	
	}
}


void bsort(node xs)
  requires xs::lls<n,k,sm> & n>0 & Term[n-k]
  ensures xs::sll<n,sm1> & sm1<=sm;
     /*
	requires xs::ll<n> & n>0
	ensures xs::sll<n, _, _>;
     */
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}

void skip()


/*
# bubble-1.ss --esl --en-inf -p bubble

Can we tidy printing for --esl. It could be
an option that is on by default (e.g. --print-tidy)

 --------------------
!!!dumping for bubble$node FAIL2
!!!  
id: 423; caller: []; line: 51; TIME: 0.83; classic: false; kind: POST; hec_num: 5; evars: [n_2565,k1_2566,sm1_2567]; infer_vars: []; c_heap: emp
 checkentail r_1706::lls<flted_35_1704,k_1702,sm_1703>@M * xs'::node<v_1705,r_1528>@M * 
r_1528::node<v_1527,r_1706>@M&0<n_1540 & 0<n_1540 & 0<n_1540 & 0<n_1540 & 
k1_1566!=n_1540 & n_1540=flted_35_1704+1 & k1_1566<n_1540 & 
v_1705<=sm1_1567 & k1_1566=k_1702 & sm1_1567=sm_1703 & 0<n_1540 & 0<n_1540 & 
k!=n & n=flted_35_1526+1 & k<n & v_1527<=sm & k=k_1524 & sm=sm_1525 & 0<n & 
xs=xs' & k!=n & r_1528!=null & !(v_bool_57_1175') & r_1528!=null & 
!(v_bool_57_1175') & flted_35_1526=n_1540 & k_1524=k_1541 & 
sm_1525=sm_1542 & k_1541!=n_1540 & k_1524<=flted_35_1526 & 0<=k_1524 & 
tmp_2563 & k1_1566=1+k_1541 & sm1_1567<=sm_1542 & k_1541!=n_1540 & 
k_1541<=n_1540 & 0<=k_1541 & v_1705<v_1527 & !(v_bool_65_1173') & 
v_1705<v_1527 & !(v_bool_65_1173') & v_1527=val_70_1736 & 
v_1705=val_71_1748 & flag_2564 & v_boolean_76_1174' & flag_2564 & 
res=v_boolean_76_1174'&{FLOW,(26,27)=__norm}[]
 |-  (exists n_2565,k1_2566,sm1_2567: xs::lls<n_2565,k1_2566,sm1_2567>@M&
{FLOW,(26,27)=__norm})[]. 




!!! processing primitives "["prelude_inf.ss";"prelude.ss"]
Starting Omega...oc
warning fast_imply : not normalisedwarning fast_imply : not normalised

 bsort verifies but not bubble..
*/
