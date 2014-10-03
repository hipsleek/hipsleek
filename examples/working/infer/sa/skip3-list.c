struct node3{
  int val;
  struct node3* n1;
  struct node3* n2;
  struct node3* n3;
};

/*@
skipll3<> == self=null or self::node3<_,null,n2,n3> * n2::skipll2<n3> * n3::skipll3<>;

skipll2<q> == self=q or self::node3<_,n1,n2,null> * n2::skipll2<q> * n1::lseg<n2> & self != q;

//lseg2<q> == seff=q or self::node3<_,_,n2,null> * n2::lseg2<q>;

lseg<q> == self=q or self::node3<_,n1,null,null> * n1::lseg<q> & self != q;
*/
/*@
HeapPred H1(node3 a,node3@NI b).
HeapPred H2(node3 a,node3@NI b).
HeapPred H3(node3 a).
*/
int skip2(struct node3* l)
/*@
infer[H3] requires H3(l) ensures res>0;
*/
/*
 requires l::skipll3<>
  ensures res>0;
*/
{
	if (!l) return 1;
	else return skip2(l->n3) && l->n1==NULL && skip1(l->n2, l->n3);
}

int skip1(struct node3* l, struct node3* e)
/*@
infer[H2] requires H2(l,e) ensures res>0;
*/
/*
  requires l::skipll2<e>
    ensures res>0;
*/
{
	if (l==e) return 1;
	else return (l!=e) && skip0(l->n1, l->n2) && l->n3 == NULL && skip1(l->n2, e);
}

int skip0(struct node3* l, struct node3* e)
/*@
infer[H1] requires H1(l,e) ensures res>0;
*/
/*
  requires l::lseg<e>
  ensures res>0;
 */
{
  if (l == e) return 1;
    else return (l) && l->n2 == NULL && l->n3 == NULL && skip0(l->n1, e);
}


