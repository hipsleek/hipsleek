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

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node ra, node b, node rb, node@NI c).

void lscan(ref node cur, ref node prev, node sent)
/*
requires cur::ll<sent> * prev::lseg<sent> & cur!=null 
ensures prev'::ll<sent>  & cur'=sent ;
requires cur::lseg<sent> * prev::ll<sent> & cur!=sent 
ensures prev'::ll<sent>  & cur'=sent ;
*/ 
  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
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
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);

}

/*

[ H(cur,prev,sent@NI) --> cur::node<val_0,next_1>@M * 
  H_2(next_1,prev@NI,sent@NI) * H_3(prev,cur@NI),
                                                         ^^sent

 H_3(prev,cur@NI) * cur::node<val_0,prev>@M&cur=cur_909 & 
  cur'=cur_909 & prev'=null 
     --> H(cur',prev',sent@NI),

 H_2(next_1,prev@NI,sent@NI) * H_3(prev,cur@NI) * 
  cur::node<val_0,prev>@M&cur=cur_909 & cur'=next_1 & cur'!=sent & 
  cur'!=null 
    --> H(cur',cur_909,sent@NI),

 H_2(next_1,prev@NI,sent@NI) * H_3(prev,cur@NI) * 
  cur::node<val_0,prev>@M&cur=prev' & cur'=next_1 & 
  cur'=sent 
     --> G(cur,cur',prev,prev',sent@NI),

 H_2(next_1,prev@NI,sent@NI) * H_3(prev,cur@NI) * 
  cur::node<val_0,prev>@M&cur=prev' & cur'=next_1 & 
  cur'=sent 
    --> G(cur,cur',prev,prev',sent@NI),

 H_2(next_1,prev@NI,sent@NI) * 
  G(prev_921,cur',prev_933,prev',sent@NI)&cur=prev_921 & next_1!=sent & 
  prev_933=null & next_1=null 
    --> G(cur,cur',prev,prev',sent@NI),

 G(next_1,cur',cur,prev',sent@NI)&next_1!=sent & 
  next_1!=null 
    --> G(cur,cur',prev,prev',sent@NI)]

HeapPred H(node a, node b, node@NI c).
HeapPred H_3(node prev, node@NI cur).
HeapPred H_2(node next_1, node@NI prev, node@NI sent).
HeapPred G(node a, node ra, node b, node rb, node@NI c).

 id: 1; caller: []; line: 36; classic: false; kind: BIND; hec_num: 5; evars: []; infer_vars: [H,G]; c_heap: emp
 checkentail H(cur,prev,sent)&cur=cur' & prev=prev' & sent=sent'&{FLOW,(22,23)=__norm}[]
 |-  cur'::node<val_76',next_77'>@L&{FLOW,(1,25)=__flow}[]. 
hprel_ass: [ H(cur,prev,sent) --> cur::node<val_0,next_1>@M * 
  H_2(next_1,prev,sent) * H_3(prev,cur)]
res:  [
  H_2(next_1,prev,sent) * H_3(prev,cur) * cur::node<val_0,next_1>@M&cur=cur' & prev=prev' & sent=sent' & val_76'=val_0 & next_77'=next_1&{FLOW,(22,23)=__norm}[]
  ]
=======================


[ H(cur_960,prev_961,sent_962) ::= cur_960::node<val_0,next_1>@M * 
H_2(next_1,prev_961,sent_962) * H_3(prev_961,cur_960),
 G(cur_966,next_36_967,prev_968,prev_969,sent_970) ::= 
 H_3(prev_968,cur_966) * cur_966::node<val_0,prev_968>@M&
 cur_966=prev_969 & next_36_967=sent_970
 or G(cur_966,next_36_967,prev_933,prev_969,sent_970)&
    next_1!=sent_970 & prev_933=null & next_1=null
 or G(next_1,next_36_967,cur_966,prev_969,sent_970)&
    next_1!=sent_970 & next_1!=null
 ,
 H_2(next_36_963,prev_964,sent_965) ::= 
 emp&!((next_36_963!=sent_965 & next_36_963=null)) & next_36_963=sent_965
 or emp&next_36_963!=sent_965 & next_36_963=null
 ]

=======

[ H(cur_947,prev_948,sent_949) ::= 
   cur_947::node<val_0,next_1>@M * 
    H_2(next_1,prev_948,sent_949) * H_3(prev_948,cur_947)
   \/  cur_947::node<val_0,next_1>@M * 
    H_2(next_1,prev_948,sent_949) * H_3(prev_948,cur_947)
   \/  cur_947::node<val_0,next_1>@M * 
    H_2(next_1,prev_948,sent_949) * H_3(prev_948,cur_947),

G(cur_950,cur_951,prev_952,prev_953,sent_954) ::= 
   G(cur_950,cur_951,prev_933,prev_953,sent_954)
     &next_1!=sent_954 & prev_933=null & next_1=null
\/  G(next_1,cur_951,cur_950,prev_953,sent_954)
       &next_1!=sent_954 & next_1!=null
\/  H_2(cur_951,prev_952,sent_954) * H_3(prev_952,prev_953) 
        * prev_953::node<val_0,prev_952>@M&cur_950=prev_953 
        & cur_951=sent_954,
H_3(prev,cur) ::= NONE,

H_2(next_36_944,prev_945,sent_946) ::= 
      emp & next_36_944=null & next_36_944!=sent_946
   \/  NONE \/  NONE]
*
*/
