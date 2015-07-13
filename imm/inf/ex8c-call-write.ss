data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 c.fst = 5;
 return x;
}

/********************
# ex8c.ss --esl

We obtained:

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELASS [P1]: ( P1(a)) -->  (a=@M | a=@A),
RELDEFN P2: ( v=res & w_1452=5 & a<:@L & P1(a)) -->  P2(a,b_1451,v,res,w_1452)]


# Why is there a HOLE in residue?

id: 0; caller: []; line: 13; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [ P1,P2]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail c::cell<v>@a&P1(a) & c'=c & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  c'::cell<fst_13_1442'>@L&{FLOW,(1,28)=__flow#E}[]. 
pure rel_ass: [RELASS [P1]: ( P1(a)) -->  a<:@L]
ho_vars: nothing?
res:  1[
   Hole[1471]&P1(a) & c'=c & fst_13_1442'=v & a<:@L&{FLOW,(4,5)=__norm#E}[]
   ]

# How come we got. It seems incidental connection
between a and b is lost.

RELDEFN P2: ( v=res & w_1452=5 & a<:@L & P1(a)) -->  P2(a,b_1451,v,res,w_1452)]

What happen to a<:b_1451 on the LHS

# Can we later derive pre-condition before post-condition.

Combining:
 [RELASS [P1]: ( P1(a)) -->  a<:@L,
 RELASS [P1]: ( P1(a)) -->  (a=@M | a=@A),

Gives:
 RELASS [P1]: P1(a)) -->  a=@M



*********************/


/*

To fix this a=In_1 resulting after gist

(==tpdispatcher.ml#2323==)
filter_disj@375
filter_disj inp1 : forall(v:forall(res:forall(w_1452:forall(b_1451:forall(RECa:(!((v=res & 
w_1452=5 & a<:@L & @M<:b_1451 & a<:@L)) | (((RECa=@M | RECa=@A)) & 
RECa<:@L))))))) & ((a=@M | a=@A)) & a<:@L
filter_disj inp2 :[ P1(a) & c=2, MayLoop[]]
filter_disj@375 EXIT: true

(====)
gist@378@377
gist inp1 : true
gist inp2 : a<:@L
gist@378 EXIT: a=In_1

(==fixpoint.ml#371==)
om_gist@377
om_gist inp1 : true
om_gist inp2 : a<:@L
om_gist@377 EXIT: a=In_1


*/
