

void foo(ref int i, int al, int bl)
  infer [@pre_n,@post_n] requires true ensures true;
{
  if (i<bl) {
    assert i<al;
    i= i+ 1;
    foo(i, al, bl);
  }
}

/*
GOT
*************************************
******pure relation assumption*******
*************************************
[RELASS [pre_1326]: ( pre_1326(i,al,bl,i')) -->  (i+1)<=bl & (i+1)<=al,
RELDEFN pre_1326: ( i_1341+1=i' & i+1=i' & i'<=bl' & pre_1326(i,al',bl',i_1341)) -->  pre_1326(i',al',bl',i'),
RELDEFN post_1327: ( i<bl & pre_1326(i,al,bl,i) & post_1327(1+i,al,bl,i')) -->  post_1327(i,al,bl,i'),
RELDEFN post_1327: ( i=i' & bl<=i' & pre_1326(i,al,bl,i')) -->  post_1327(i,al,bl,i')]
*************************************


!!! REL POST :  post_1327(i,al,bl,i')
!!! POST:  ((bl=i' & i<i') | (i=i' & bl<=i'))
!!! REL PRE :  pre_1326(i,al,bl,i')
!!! PRE :  false
 */

void goo(int al, int bl)
  infer [@pre_n,@post_n] requires true ensures true;
{
  int i;
  i = 0;
  foo(i, al, bl);
}


/*
expected:

case
  bl>0 & al<bl --> error
  bl<=0 \/ al >= bl --> OK

*/
