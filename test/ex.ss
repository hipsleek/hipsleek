data node {
  int val;
  node next;
}


ll<S> == self=null & S={}
  or self::node<v,q> * q::ll<S1> & S=union({v},S1)
                                           inv true;

node add_elem (int v,node lst)
  requires lst::ll<S>
  ensures res::ll<S1> & S1=union({v},S); 
{
  return new node(v,lst);
}

bool find (node lst,int k)
  requires lst::ll<S> & k in S
  ensures lst::ll<S> & res & k in S
       or lst::ll<S> & !res & k notin S;
{
  if (lst==null) return false;
  else {
    if (lst.val==k) return true;
      else return find(lst.next,k);
  }
}

void main (ref node lst,int k)
  requires lst::ll<S>
  ensures lst'::ll<S1> & k in S1;//'
{
  lst = new node(5,lst);
  lst = new node(3,lst);
  lst = add_elem(k,lst);
  lst = new node(6,lst);
  lst = new node(3,lst);
  dprint;

}


