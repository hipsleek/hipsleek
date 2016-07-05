data cell{
 int fst;
}

relation P(ann v1,ann v2).
  relation Q(ann v1,ann v2,ann v3,ann v4).

int foo2(int n,cell x, cell y)
  infer [P,Q]
  requires x::cell<v>@a * y::cell<w>@c & P(a,c)
     ensures  x::cell<v>@b * y::cell<w>@d & Q(a,c,b,d);
{
 if (n<0) return x.fst;
 return n;
}

/*

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P]: ( P(a,c)) -->  a<:@L,
RELDEFN Q: ( d_1484=@A & a<:@L & a<:b_1483 & P(a,c)) -->  Q(a,c,b_1483,d_1484),
RELDEFN Q: ( d_1484=@A & a<:b_1483 & P(a,c)) -->  Q(a,c,b_1483,d_1484)]
*************************************

how come d=@A ? (FIXED  now c<:d)



Entail (1) : Valid. 

Residue:
 <1>(exists b_50,d_49: y::cell<w>@[@c, @d_49] * x::cell<v>@[@a, @b_50]&res=v_int_13_1471' & v_int_13_1471'=v & a<:@L & n'=n & x'=x & y'=y & P(a,c) & n'<0 & v_bool_13_1472' & a<:b_50 & v_1481=v & c<:d_49 & w_1482=w&{FLOW,(20,21)=__norm#E}[]
 inferred rel: [RELDEFN Q: ( a<:@L & a<:b_50 & c<:d_49 & P(a,c)) -->  Q(a,c,b_50,d_49)]
[[ COND ==>  SEARCH ==>  Match(x,x) ==>  SEARCH ==>  Match(y,y) ==> ]]


(==immutable.ml#467==)
pick_wekeast_instatiation@7
pick_wekeast_instatiation inp1 : y::cell<w>@[@c, @d_1484] * x::cell<v>@[@a, @b_1483]&!(v_bool_13_1472') & 
0<=n' & P(a,c) & y'=y & x'=x & n'=n & res=n' & a<:b_1483&
{FLOW,(4,5)=__norm#E}[]
pick_wekeast_instatiation inp2 : emp&Q(a,c,b_1483,d_1484) & v_1481=v & w_1482=w & a<:b_1483 & v_1481=v&
{FLOW,(4,5)=__norm#E}[]
pick_wekeast_instatiation@7 EXIT:(Some( d_1484=@A),None)

*/
