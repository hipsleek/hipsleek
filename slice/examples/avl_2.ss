data node {
	int val;
	node left;
	node right;
}

avl<n, h, s, B> ==
	self = null & h = 0 & n = 0 & s = 0 & B = {} or
	self::node<v, p, q> * p::avl<n1, h1, s1, B1> * q::avl<n2, h2, s2, B2>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
		& -1 <= h1 - h2  <= 1
		& v >= 0
		& s = ($ v) + s1 + s2
		& B = union(B1, B2, {$ v})
	inv h >= 0 & n >= 0 & $ n >= h;

/*
avl<n, h, s1, s2> ==
	self = null & h = 0 & n = 0 & s1 = 0 & s2 = 0 or
	self::node<v, p, q> * p::avl<n1, h1, s11, s12> * q::avl<n2, h2, s21, s22>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
		& -1 <= h1 - h2  <= 1
		& v >= 0
		& s1 = ($ v) + s11 + s12
		& s2 = 1 + ($ v) + s21 + s22
	inv h >= 0 & n >= 0 & $ n >= h;
*/

/*
avl<n, h> ==
	self = null & h = 0 & n = 0 or
	self::node<v, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
		& -1 <= h1 - h2  <= 1
	inv h >= 0 & n >= 0 & $ n >= h;
*/

/*
(SLICE[h,h1,h2]:
   [<>(-1+h1)<=h2(IN)& <, 18, []>(-1+h2)<=h1(IN)]
   [exists1(max_162:<, 17, []>h=max_162+1 & <, 163, []>max_162=max(h1,h2))]
   alias set:[@]
 SLICE[n,n1,n2]:
   [<, 16, []>n=1+n1+n2(IN)]
   [<>true]
   alias set:[@]
 SLICE[v]:
   [<, 20, []>0<=v(IN)]
   [<>true]
   alias set:[@]
 SLICE[s,s1,s2,v]:
   [<, 21, [v]>s=s1+s2+v(IN)]
   [<>true]
   alias set:[@]
 SLICE[B,B1,B2,v]:
   [<, 22, [v]>B=union(B1,B2,{v})(IN)]
   [<>true]
   alias set:[@]))
*/
