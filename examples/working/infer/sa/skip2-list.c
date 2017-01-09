struct node2{
	int val;
	struct node2 * n;
	struct node2 *s;
};

/*@
skipll<> == self=null 	or  self::node2<_,p,q> * q::skipll<> * p::lseg<q>;

lseg<q> ==  self=q or self::node2<_,n,null>* n::lseg<q> & self != q;
*/
/*@
HeapPred H1(node2 a).
HeapPred H2(node2 a,node2@NI b).
//HeapPred H2P(node2 a,node2 b).
*/

int skip1(struct node2 * l)
/*@
infer[H1] requires H1(l) ensures res=1;
//requires l::skipll<> ensures res=1;
*/
{
	if (!l) return 1;
	else {
          /* int i1 = skip1(l->s); */
          /* int i2 = skip0(l->n,l->s); */
          /* if (i1==1 && i2==1) return 1; */
          /* else return 0; */
           return skip1(l->s) && skip0(l->n,l->s);
        }
}



int skip0(struct node2* l, struct node2* e) 
/*@
infer[H2] requires H2(l,e)  ensures res=1;
//requires l::lseg<e> & e!=null ensures res=1;
*/
{
  if (l == e) return 1;
  else{
    if (l) {
      if (l->s == NULL) {
        if ( skip0(l->n, e) ==1 ) return 1;
        else return 0;
      }
      else return 0;
    }
    else return 0;
  }
}


