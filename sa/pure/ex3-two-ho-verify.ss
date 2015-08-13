
data str {
  int val;
  str next;
}

relation P1(int a).

relation P(int a) == a=0.
relation Q(int a, int b).


HeapPred H(str a).
HeapPred G(str a, str b).

  H_v<j> == self::str<v1,q> * q::H_v<j_p> & j=0 & j_p=1
  or self::str<v1,q> * q::H_v<j_p> & j!=0 & j_p=0
  or self=null
 ;

G_v<j> == self::str<v,q> * q::G_v<j_p> & j=0 & j_p=1 & v=1
  or self::str<v,q> * q::G_v<j_p> & j!=0 & j_p=0 & v=2
  or self=null
 ;

G_v_ho<P1> == self::str<v,q> * q::G_v_ho<P1> & P1(v)
  or self=null
 ;

relation PO(int n, int m).

     void while1(ref int i, ref int j, ref str s)

 requires s::H_v<j> 
 ensures s'::G_v<j>; //'

/*
 requires s::H_v<> 
 ensures s'::G_v_ho<P>; //'
*/
//infer [P,Q] requires P(s) ensures Q(s,s');//'
{
  if (s!=null) {
    // dprint;
    if (j==0){
      s.val = 1;
      j=1;
    }
    else{
      s.val = 2;
      j=0;
    }
    i++;
    dprint;
    while1(i, j, s.next);
  }
}
