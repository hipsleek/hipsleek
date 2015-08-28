data node {
 int h;
 node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

HeapPred H(node x, bool flag). // non-ptrs are @NI by default
  PostPred G(node x, bool flag). // non-ptrs are @NI by default


ll_alter<> == self::node<3,_>
  or self::node<v,q>*q::ll_alter<>
  ;

ll_alter_data<flag> == self::node<3,_>
  or self::node<2,q>*q::ll_alter_data<false> & flag
  or self::node<1,q>*q::ll_alter_data<true> & !flag
  ;

lseg_alter<p> == self=p
  or self::node<v,q>*q::lseg_alter<p>
  ;

lseg_alter_data<p,flag> == self=p
  or self::node<v,q>*q::lseg_alter_data<p,false> & flag
  or self::node<v,q>*q::lseg_alter_data<p,true> & !flag
  ;


bool check_one_two_ok (ref node p, ref bool flag)
/*
infer [H,G]
  requires H(x,flag)
  ensures G(x,flag);
*/
//  requires p::ll_alter<> ensures p::lseg_alter<p'> * p'::node<_,_>;
 requires p::ll_alter_data<flag> ensures p::lseg_alter_data<p',_> * p'::node<_,_>;
{
  if (p.h != 3) {
    if (flag) {
      dprint;
      if (p.h == 2){
        assert false;
        return false;
      }
      flag=false;
    }
    else {
      if (p.h == 1) {
        assert false;
        return false;
      }
      flag=true;
    }
    p = p.next;
    return check_one_two_ok(p,flag);
  }
  return true;
}

