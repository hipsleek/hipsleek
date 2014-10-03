/* selection sort */

data node {
	int val; 
	node next; 
}

/* fail to prove for delete_min
bnd1<n,mi,mx> == 
  self = null & n = 0 & mi = \inf & mx=-\inf or 
  self::node<d, p> * p::bnd1<n-1,tmi,tmx> & mi=min(d,tmi) 
  & mx=max(d,tmx) & -\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n>0 & mi<=mx & -\inf<mi & mx<\inf 
  ;
*/

// 3 cases needed to prove delete_min
bnd1<n,mi,mx> == self = null & n = 0 & mi = \inf & mx=-\inf or 
  self::node<d, p> * p::bnd1<n-1, tmi,tmx> & mi = min(d, tmi) & mx=max(d,tmx)  & -\inf<d<\inf 
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf |
      self!=null & n>1 & mi<=mx & -\inf<mi & mx<\inf;

sll<n, mi,mx> == self = null & mi = \inf & mx = -\inf & n = 0
 or self::node<mi, null> & n=1 & -\inf<mi<\inf & mi=mx
 or self::node<mi, q> * q::sll<n-1, qs,mx> & -\inf<mi<\inf & mi <= qs
      &  q!=null //& -\inf<mx<\inf //& n>1
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n=1 & mi=mx & -\inf<mi<\inf  |
      self!=null & n>1 & mi<=mx  & -\inf<mi & mx<\inf;

/* NOT sufficient for proving selection_sort
sll<n, mi,mx> == 
   self = null & mi = \inf & mx = -\inf & n = 0
 or self::node<mi, null> & n=1 & -\inf<mi<\inf & mi=mx
 or self::node<mi, q> * q::sll<n-1, qs,mx> & -\inf<mi<\inf & mi <= qs
      &  q!=null //& -\inf<mx<\inf //& n>1
  inv self=null & n=0 & mi=\inf & mx=-\inf |
      self!=null & n>0 & mi<=mx  & -\inf<mi & mx<\inf
;
*/

int find_min(node x)
     requires x::bnd1<n, mi,mx> & n > 0
     ensures x::bnd1<n, mi,mx> & res = mi & -\inf<res<\inf;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{	
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

void delete_min(ref node x, int a)
  requires x::bnd1<n, mi,mx> & n >= 1 & a = mi
  case {
    n=1 -> ensures x'=null;
    n!=1 -> ensures x'::bnd1<n-1,mi1,mx> & mi<=mi1;
    }  
     //& mi<=mi1  
     //& (n>1 & mx1=mx & mi<=mi1 | n=1 & mx1=(-\inf) & mi1=\inf);
/*
  requires x::bnd1<n, mi,mx> & n >= 1 & a = mi
  case {
    n=1 -> ensures x'=null ;
   n!=1 -> ensures x'::bnd1<n-1, mi1,mx> & x'!=null & mi1 >= mi;//'
  }
*/
{
	if (x.val == a)
		x = x.next;
	else {
        //assume false;
		bind x to (_, xnext) in {
                   //assume xnext'=null or xnext'!=null;
			delete_min(xnext, a);
		}
	}
}

node selection_sort(ref node x)
/*
	requires x::bnd1<n, mi,mx> & n > 0 
	ensures res::sll<n, mi,mx> & x' = null;//'
    // VERY slow for bytecode; cannot verify
    Native verification time: 106.5 second(s)
	Time spent in main process: 90.47 second(s)
	Time spent in child processes: 16.03 second(s)
*/
/*
  WHY use existential? and why so complex LHS?
 checkentail (exists x_896,
tmp_39': tmp_39'::sll<n_891,mi_892,mx_893>@M[0][Orig][LHSCase] * 
v_node_116_643'::node<mi_866,tmp_39'>@M[Orig]&0<n & n!=1 & tmp_40'=null & 
n=n_865 & mi=mi_866 & mx=mx_867 & ((x=null & n=0 & mi=\inf & mx+(\inf)=0) | 
(x!=null & n=1 & mi=mx & 0<(mi+(\inf)) & mi<(\inf)) | (x!=null & 1<n & 
mi<=mx & 0<(mi+(\inf)) & mx<(\inf))) & ((x=null & n_865=0 & mi_866=\inf & 
mx_867+(\inf)=0) | (x!=null & n_865=1 & mi_866=mx_867 & 0<(mi_866+(\inf)) & 
mi_866<(\inf)) | (x!=null & 1<n_865 & mi_866<=mx_867 & 0<(mi_866+(\inf)) & 
mx_867<(\inf))) & n_865=n_874 & mi_866=mi_875 & mx_867=mx_876 & n_874!=1 & 
((x=null & n_865=0 & mi_866=\inf & mx_867+(\inf)=0) | (x!=null & n_865=1 & 
mi_866=mx_867 & 0<(mi_866+(\inf)) & mi_866<(\inf)) | (x!=null & 1<n_865 & 
mi_866<=mx_867 & 0<(mi_866+(\inf)) & mx_867<(\inf))) & n_874=flted_66_887+
1 & mi_875<=mi1_888 & n_874!=1 & ((x=null & n_874=0 & mi_875=\inf & mx_876+
(\inf)=0) | (x!=null & n_874=1 & mi_875=mx_876 & 0<(mi_875+(\inf)) & 
mi_875<(\inf)) | (x!=null & 1<n_874 & mi_875<=mx_876 & 0<(mi_875+(\inf)) & 
mx_876<(\inf))) & x_896!=null & !(v_bool_110_644') & x_896!=null & 
!(v_bool_110_644') & flted_66_887=n_891 & mi1_888=mi_892 & mx_876=mx_893 & 
n_891=1 & ((x_896=null & flted_66_887=0 & mi1_888=\inf & mx_876+(\inf)=0) | 
(x_896!=null & flted_66_887=1 & mi1_888=mx_876 & 0<(mi1_888+(\inf)) & 
mi1_888<(\inf)) | (x_896!=null & 1<flted_66_887 & mi1_888<=mx_876 & 
0<(mi1_888+(\inf)) & mx_876<(\inf))) & mi_892=mx_893 & x'=null & n_891=1 & 
((x_896=null & n_891=0 & mi_892=\inf & mx_893+(\inf)=0) | (x_896!=null & 
n_891=1 & mi_892=mx_893 & 0<(mi_892+(\inf)) & mi_892<(\inf)) | 
(x_896!=null & 1<n_891 & mi_892<=mx_893 & 0<(mi_892+(\inf)) & 
mx_893<(\inf))) & res=v_node_116_643'&{FLOW,(22,23)=__norm})[]
 |-  (exists n_32,mi_33,mx_34: res::sll<n_32,mi_33,mx_34>@M[0][Orig][LHSCase]&
x'=null & n=n_32 & mi=mi_33 & mx=mx_34&{FLOW,(22,23)=__norm})[]. 

 |-  (exists n_1002,mi_1003,
mx_1004: res::sll<n_1002,mi_1003,mx_1004>@M[0][Orig][LHSCase]&true&
{FLOW,(22,23)=__norm})[]
*/
/* OK
 requires x::bnd1<n, mi,mx> & n =1
 ensures res::sll<n,mi,mx> & mi=mx & x'=null;
*/
/*
Total verification time: 449.31 second(s)
	Time spent in main process: 390.55 second(s)
	Time spent in child processes: 58.76 second(s)
 verified after adding assumption that integer values
 cannot be fictitious
*/
 requires x::bnd1<n, mi,mx> & n > 0 
 case {
    n=1 -> ensures res::sll<n, mi,mx> & n=1 & mi=mx & x' = null;//'
    n!=1 -> ensures res::sll<n, mi,mx> & n>1 & res!=null & x' = null;//'
 }
{
	int minimum;
	node tmp, tmp_null = null;	

	minimum = find_min(x);
	delete_min(x, minimum);

	if (x == null)
		return new node(minimum, tmp_null);
	else
	{
		tmp = selection_sort(x);
        //assert false;
		return new node(minimum, tmp);
	}
}












