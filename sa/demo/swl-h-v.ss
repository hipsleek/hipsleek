data node{
	int val;
	node next;
}

/*
ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self!=p & M=union(M2,{self})
inv true;
*/
/*
ll<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::ll<s> & self!=s 
inv self!=s ;

lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;
*/
lx<g:node,s> == self=s
  or self!=s & self=null
  or self::node<_,nxt> * nxt::lx<_,s> & self!=s 
inv true ;

HeapPred HP9(node a).

H1<sent> == self::node<_,n>@M * n::HP_948<sent>;

H2<sent> ==
  // self=sent
 emp&self=null & self!=sent
  or prev::H2<sent> * self::node<_,prev>@M 
 or HP9(next_46_947);

 HP_948<s> ==
 emp&self=s or
 emp & self!=s &self=null
   or self::node<_,p> * p::HP_948<s>&self!=s;

G1<cur,sent> == prev::H2<sent> * self::node<_,prev>@M&cur=sent;

lemma  "V1" self::HP_948<s> <-> self::H2<s>;
   /*
HeapPred H(node a, node b, node@NI c).
HeapPred H1(node a,  node@NI c).
HeapPred H2(node a,  node@NI c).
PostPred G(node a, node ra, node b, node rb, node@NI c).

PostPred G1(node ra,  node rb, node@NI c).
   */

void lscan(ref node cur, ref node prev, node sent)
/*
  requires cur::node<_,n> * n::lx<_,sent> * prev::lx<_,sent> & cur!=sent
// ensures prev'::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
  ensures  prev'::node<_,p> * p::lx<_,sent>  & cur'=sent &prev'!=sent ;//'
*/
/*
  infer [H1,H2,G1]
  requires H1(cur,sent) * H2(prev,sent)
  ensures G1(cur',prev',sent);
*/
requires cur::H1<sent> * prev::H2<sent> & cur!=sent
// requires cur::node<_,n> * n::HP_948<sent> * prev::H2<sent> & cur!=sent
    ensures prev'::G1<cur',sent> &prev'!=sent;//'

//  requires cur::node<_,n> * n::HP_948<sent> * prev::H2<sent> & cur!=sent
//  ensures  prev'::node<_,p> * p::H2<sent>  & cur'=sent &prev'!=sent ;//'
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
      //assume false;
      return;
  }
  //dprint;
  if (cur == null) {
      // change direction;
    node tmp = cur;
      cur = prev;
      //prev = null;
      prev = tmp;
  }
  //dprint;
  lscan(cur,prev,sent);

}

