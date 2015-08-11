
data str {
  int val;
  str next;
}

relation P1(int a).

relation P(int a) == a=0.
relation P(int a) == true.
relation Q(int a, int b).


HeapPred H(str a).
HeapPred G(str a, str b).

H_v<> == self::str<v1,q> * q::H_v<>
  or self=null
 ;

G_v<> == self::str<v,q> * q::G_v<> & v=0
  or self=null
 ;

G_v_ho<P1> == self::str<v,q> * q::G_v_ho<P1> & P1(v)
  or self=null
 ;

relation PO(int n, int m).

void while1(ref str s)

 requires s::H_v<> 
 ensures s'::G_v<>; //'

/*
 requires s::G_v_ho<P_true> 
 ensures s'::G_v_ho<P>; //'
*/
//infer [P,Q] requires P(s) ensures Q(s,s');//'
{
  if (s!=null) {
    // dprint;
    s.val = 0;
    //dprint;
    while1(s.next);
  }
}


/*
Checking procedure while1$str...
Post condition cannot be derived:
  (may) cause: do_unmatched_rhs : q_1510::G_v<>@M(may)

---------
todo: induction

 */
