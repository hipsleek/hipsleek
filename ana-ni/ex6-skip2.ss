data node2{
	int val;
	node2 n;
	node2 s;
}

relation R(node2 x).
relation P(node2 x).
relation Q(node2 x).

bool skip1(node2 l)
  infer [@ana_ni,R,P,Q]
  requires R(x)
  ensures true;
{
  if (l==null) return true;
  else return skip1(l.s) && skip0(l.n,l.s);
}

bool skip0(node2 l, node2 e) 
  infer [@ana_ni,Q,P,R]
  requires P(x) & Q(y)
  ensures true;
{
  if (l == e) return true;
  else if (l==null) return false;
  else  return skip0(l.n, e) && l.s == null;
}

/*

Proving binding in method skip0$node2~node2 for spec  EAssume
   htrue&{FLOW,(4,5)=__norm#E}[]
   struct:EBase
            htrue&{FLOW,(4,5)=__norm#E}[], Line 23

( [(,1 ); (,2 ); (,1 ); (,2 )]) bind: node  l'::node2<val_27_1696',n_27_1697',s_27_1698'>@L cannot be derived from context
1 File "ex6-skip2.ss",Line:27,Col:21

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
 Failed States:
 [
  Label: [(,1 ); (,2 ); (,1 ); (,2 )]
  State:
    fe_kind: MAY
    fe_name: logical bug
    fe_locs: {
        fc_message:  l'!=null & l'!=e |-  1<l'. LOCS:[26;20;25;0] (may-bug)
        fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
      }
    [[empty]]
  ]1 File "ex6-skip2.ss",Line:27,Col:21

 */
