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

void lscan(node@R cur, node@R prev, node sent)
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
 
 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
  & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;
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
      cur = prev;
      prev = null;
  }
  // dprint;
  lscan(cur,prev,sent);

}

/*
# swl-i.ss

We have two pre-obligations :

!!! PRE-OBLIGATION:
 HP_903(prev_940,cur_943,sent_938) * cur_943::node<val_36_939,prev_940>@M
  & prev_941=null & cur_942=cur_943 
  --> cur_942::node<val_36_900,next_36_901>@M * 
  HP_902(next_36_901,prev_941,sent_938) * HP_903(prev_941,cur_942,sent_938)
!!! PRE-OBLIGATION:
 HP_902(next_36_947,prev_946,sent_948) * HP_903(prev_946,cur_944,sent_948) * 
  cur_944::node<val_36_945,prev_946>@M&next_36_947!=null 
  & next_36_947!=sent_948 
  --> next_36_947::node<val_36_900,next_36_901>@M * 
  HP_902(next_36_901,cur_944,sent_948) * HP_903(cur_944,next_36_947,sent_948)

which resulted in below. However, for these pre-obligation
you need to run it under classic always. Have you use wrapper
method in wrapper.ml to ensure this?

[ HP_903(prev_940,cur_943,sent_938) &  prev_941=null 
    --> HP_902(prev_940,prev_941,sent_938),

 emp&prev_941=null --> HP_903(prev_941,cur_942,sent_964),
 
 HP_902(next_36_947,prev_946,sent_948)&next_36_947!=null & 
  next_36_947!=sent_948 --> next_36_947::node<val_36_965,next_36_966>@M 
  * HP_967(next_36_966,prev_946,sent_948),
 
 HP_967(next_36_966,prev_946,sent_948) 
  |#| cur_944::node<val_36_945,prev_946>@M 
     --> HP_902(next_36_966,cur_944,sent_948),

 HP_903(prev_946,cur_944,sent_948) 
  * cur_944::node<val_36_945,prev_946>@M& next_36_947!=null 
  &  next_36_947!=sent_948 --> HP_903(cur_944,next_36_947,sent_948)]

We also obtained below but I am not sure what are they?
What are they?

*************************************************
*******relational assumptions (pre-assumptions)********
****************************************************
[ HP_902(next_36_901,prev,sent)
   & next_36_901=sent  --> emp,
 HP_902(next_36_901,prev,sent)
   &next_36_901!=sent & next_36_901=null --> emp]

Assuming these assumptions are correct, we would still have to
synthesize their predicate definitions. Do not also forget to
dump the header for new predicate introduced such as:

 HP_967(next_36_966,prev_946,sent_948) 

One possible next candidate is HP_903:

 HP_903(prev_940,cur_943,sent_938) &  prev_941=null 
    --> HP_902(prev_940,prev_941,sent_938),

 HP_903(prev_946,cur_944,sent_948) 
  * cur_944::node<val_36_945,prev_946>@M& next_36_947!=null 
  &  next_36_947!=sent_948 --> HP_903(cur_944,next_36_947,sent_948)]
 emp&prev_941=null --> HP_903(prev_941,cur_942,sent_964),

We have two choices
(i)  HP_903(prev_940,cur_943,sent_938) 
     ::= HP_902(prev_940,null,sent_938),

(ii)  HP_903(prev_946,cur_944,sent_948) 
  * cur_944::node<val_36_945,prev_946>@M& next_36_947!=null 
  &  next_36_947!=sent_948 --> HP_903(cur_944,next_36_947,sent_948)]
 emp&prev_941=null --> HP_903(prev_941,cur_942,sent_964),

I would suggest that we try (1), which would lead to two pre-obligations:


(i)  HP_903(prev_946,cur_944,sent_948) 
     * cur_944::node<val_36_945,prev_946>@M& next_36_947!=null &  
      next_36_947!=sent_948 --> HP_902(cur_944,null,sent_948)
(ii)  emp&prev_941=null --> HP_902(prev_941,null,sent_964)

HP_903(prev_941,cur_942,sent_964),

===========================================================

shape_infer is failing for some reason
(i) provide an option --sa-dis-infer
    to disable shape_infer
(ii) try to fix the problem such that a
     less accurate result is obtained rather
     than an exception

Context of Verification Failure: 1 File "swl-i.ss",Line:32,Col:10
Last Proving Location: 1 File "swl-i.ss",Line:51,Col:2

ERROR: at _0:0_0:0 
Message: shape analysis: FAIL
 
ExceptionFailure("shape analysis: FAIL")Occurred!

Error(s) detected at main 
Stop Omega... 101 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("shape analysis: FAIL")

HeapPred H(node a, node b, node@NI c).
HeapPred H_3(node prev, node@NI cur, node@NI sent).
HeapPred H_2(node next_1, node@NI prev, node@NI sent).
HeapPred G(node a, node ra, node b, node rb, node@NI c).

 H(cur,prev,sent) --> cur::node<val_0,next_1>@M * 
  H_2(next_1,prev,sent) * H_3(prev,cur,sent).


 State:H_2(next_36_901,prev,sent) * H_3(prev,cur,sent) * cur_909::node<val
_36_900,prev_908>@M&cur=cur_909 & prev=prev_908 & sent=sent' & n_34'=next_36_901
 & next_36_901=next_38_907 & cur_909=prev_921 & cur_920=n_34' & cur_920!=sent' &
 !(v_bool_42_880') & cur_920!=sent' & !(v_bool_42_880') & cur_920=null & v_bool_
46_881' & cur_920=null & v_bool_46_881' & cur'=prev_921 & prev'=null&{FLOW,(22,2
3)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [1; 2; 0]
;
 H_3(prev,cur,sent) * cur::node<val_0,prev>@M&cur_920=null & 
  next_1=null & cur=cur_909 & cur_920=next_1 & cur'=cur_909 & 
  prev'=null --> H(cur',prev',sent).

 H_2(next_1,prev,sent) * H_3(prev,cur,sent) * 
  cur::node<val_0,prev>@M&cur=cur_909 & cur'=next_1 & cur'!=sent & 
  cur'!=null --> H(cur',cur_909,sent).

======

 H_2(next_1,prev,sent) * H_3(prev,cur,sent) * 
  cur::node<val_0,prev>@M&cur=prev' & cur'=next_1 & 
  cur'=sent --> G(cur,cur',prev,prev',sent).

 H_2(next_1,prev,sent) * 
  G(prev_921,cur',prev_933,prev',sent)&cur=prev_921 & next_1!=sent & 
  prev_933=null & next_1=null --> G(cur,cur',prev,prev',sent).

 G(next_1,cur',cur,prev',sent)&next_1!=sent & 
  next_1!=null --> G(cur,cur',prev,prev',sent).


//duplicate
 H_2(next_1,prev,sent) * H_3(prev,cur,sent) * 
  cur::node<val_0,prev>@M&cur=prev' & cur'=next_1 & 
  cur'=sent --> G(cur,cur',prev,prev',sent),



*/
