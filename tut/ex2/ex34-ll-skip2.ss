data node2{
  int val;
  node2 n;
  node2 s;
}


skipll<> == self=null 	or  self::node2<_,p,q> * q::skipll<> * p::lseg<q>;

lseg<q> ==  self=q or self::node2<_,n,null>* n::lseg<q> & self != q;

HeapPred H1(node2 a).
HeapPred H2(node2 a,node2@NI b).


bool skip1(node2 l)
infer[H1] requires H1(l) ensures res;
//requires l::skipll<> ensures res;
{
  if (l==null) return true;
  else {
    return skip1(l.s) && skip0(l.n,l.s);
  }
}



bool skip0(node2 l, node2 e) 
infer[H2] requires H2(l,e)  ensures res;
//requires l::lseg<e> & e!=null ensures res;
{
  if (l == e) return true;
  else{
    if (l!=null) {
      if (l.s == null) {
        if ( skip0(l.n, e) ) return true;
        else return false;
      }
      else return false;
    }
    else return false;
  }
}

