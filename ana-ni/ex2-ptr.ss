data node {
  int val;
  node next;
}

bool foo(node x) 
  requires true
  //ensures true;
  ensures res=(x=null);
{
  return (x==null);
}

int hoo(node x)
  infer [@ana_ni]
  requires x>1
  ensures true;
{
  int y = x.val;
  return y;
}

int hoo1(node x)
  requires x>1
  ensures true;
{
  int y = x.val;
  return y;

}

int hoo3(node x)
  requires x::node<v,_>
  ensures res=v;
{
  int y = x.val;
  return y;
}


int hoo2(node x)
  infer [@ana_ni]
  requires x>1
  ensures true;
{
  assert x'!=null;
  return 0;
}

/*
# ex2.ss -p hoo

int hoo(node x)
  infer [@ana_ni]
  requires x>1
  ensures true;
{
  int y = x.val;
  return y;
}

# relax bind_failure? change bind test to
      ....  |- x>1

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
 Failed States:
 [
  Label: []
  State:
    fe_kind: MUST
    fe_name: separation entailment
    fe_locs: {
        fc_message: do_unmatched_rhs : x'::node<val_19_1683',next_19_1684'>@L(must)
        fc_current_lhs_flow: {FLOW,(6,10)=__Error#E}
      }
    [[ UnmatchedRHSData]]
  ]1 File "ex2-ptr.ss",Line:19,Col:10

Context of Verification Failure: ex2-ptr.ss_17:10_17:14

Last Proving Location: ex2-ptr.ss_19:10_19:15

Procedure hoo$node FAIL.(2)
Exception Failure("bind failure exception") Occurred!

*/


