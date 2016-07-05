data node{
	int val;
	node next;
}

/*
ls<M,p> == self=p & M={}
  or self::node<_,nxt> * nxt::ls<M2,p> & self!=p & M=union(M2,{self})
inv true;
*/

ll<s> == self=null & self!=s 
  or self::node<_,nxt> * nxt::ll<s> & self!=s 
inv self!=s ;

lseg<p> == self=p 
  or self::node<_,nxt> * nxt::lseg<p> & self!=p 
inv true;

lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s 
 inv self!=s ;

HeapPred H(node a, node b, node@NI c).
PostPred G(node a, node ra, node b, node rb, node@NI c).

int lscan(node@R cur, node@R prev, node sent)
/*
requires cur::ll<sent> * prev::lseg<sent> & cur!=null 
ensures prev'::ll<sent>  & cur'=sent ;
requires cur::lseg<sent> * prev::ll<sent> & cur!=sent 
ensures prev'::ll<sent>  & cur'=sent ;

 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
   & (a=null & b=sent | a=sent & b=null)

 infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
*/
 
  requires cur::node<_,_>
  ensures true;

{

  node n;
  n = cur.next;
  if (cur == sent) {
      //assume false;
      return 1;
  }
  dprint;
  if (cur == null) {
      // change direction;
      cur = prev;
      dprint;
  }
  else {
    return 2;
  }
  dprint;
  return 3;
}

/*
# guard/return-err.ss 

Duplicated exception flows!

First dprint has one __Return flow:

 Try-Block:0::
 [
  Path: [(,0 ); (,1 )]
  State:cur::node<_,_>@M&sent=sent' & prev=prev' & cur=cur' & Anon_15=n_39' & cur'=sent' & v_bool_49_923' & cur'=sent' & v_bool_49_923'&{FLOW,(18,19)=__Return}[]
        es_var_measures 2: MayLoop[]
        es_trace: empty
        es_cond_path: [1; 0]

  ]

However, 2nd dprint has two __Return flow
This seems unnecessary disjunction for exceptional flow::

 Try-Block:0::
 [
  Path: [(,0 ); (,1 )]
  State:or[cur::node<_,_>@M&sent=sent' & prev=prev' & cur=cur' & Anon_15=n_39' & cur'=sent' & v_bool_49_923' & cur'=sent' & v_bool_49_923'&{FLOW,(18,19)=__Return}[]
           es_var_measures 2: MayLoop[]
           es_trace: empty
           es_cond_path: [1; 0]
; 
          cur::node<_,_>@M&sent=sent' & prev=prev' & cur=cur' & Anon_15=n_39' & cur'=sent' & v_bool_49_923' & cur'=sent' & v_bool_49_923'&{FLOW,(18,19)=__Return}[]
          es_var_measures 2: MayLoop[]
          es_trace: empty
          es_cond_path: [1; 0]
]
  ]
 ]



*/
