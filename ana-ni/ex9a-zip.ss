data node {
  int val;
  node next;
}

ll<n> == self=null & n=0 
  or self::node<_,q>*q::ll<n-1>
inv n>=0;

relation P(int a,int b).
relation Q(int a,int b, int c).

node zip(node x,node y)
/*
 requires x::ll<a>*y::ll<b> & a=b
 ensures res::ll<n> & n=a;
 infer[P,Q]
 requires x::ll<a>*y::ll<b> & P(a,b)
 ensures res::ll<n> & Q(a,b,n);
*/
  infer [@ana_ni]//,R]
  requires true
 ensures true;
{
  if (x==null) return x;
  else {
    // node t = new node(0,null);
    node r = new node(x.val+y.val,null);
    r.next = zip(x.next,y.next);
    return r;
  }
}

/*
# ex9a.ss

  infer [@ana_ni]//,R]
  requires true
 ensures true;

Checking procedure zip$node~node... 
!!! **typechecker.ml#564:inf_o_lst:[@ana_ni]Proving binding in method zip$node~node for spec  EAssume 
   htrue&{FLOW,(4,5)=__norm#E}[]
   struct:EBase 
            htrue&{FLOW,(4,5)=__norm#E}[], Line 233

( [(,1 ); (,2 )]) bind: node  emp&r'>1&{FLOW,(1,28)=__flow#E}[] cannot be derived from context
1 File "ex9a-zip.ss",Line:28,Col:4

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
 Failed States:
 [
  Label: [(,1 ); (,2 )]
  State:
    fe_kind: MAY
    fe_name: logical bug
    fe_locs: {
        fc_message:  r'!=null |-  1<r'. LOCS:[27;0] (may-bug)
        fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
  
 */

                             /*
[
RELDEFN _i_x_1739: ( 2<=v_node_29_1729') -->  _i_x_1739(v_node_29_1729'),
RELDEFN _i_y_1740: ( 2<=v_node_29_1728') -->  _i_y_1740(v_node_29_1728'),
RELASS [_i_y_1740,_i_x_1739]: ( _i_y_1740(y) & _i_x_1739(x)) -->  (x<=1 | 2<=y),
RELASS [_i_y_1740,_i_x_1739]: ( _i_y_1740(y) & _i_x_1739(x)) -->  (x<=1 | 2<=y),
RELASS [_i_x_1739]: ( _i_x_1739(x)) -->  x!=1]
                              */
