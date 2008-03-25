data elem {
	elem attends;
	elem next;
}

school<S> == self= null & S={}
	or self::elem<_,q> * q::school<S1> & S=union({self},S1);
// list of schools

students<N,S> == self= null & N={}
	or self::elem<a,q> * q::students<N1,S> & N=union({self},N1)
        & intersect(S,{a}) != {} ;
// list of students attending schools

elem  add_sch(elem sc, elem SC)
 requires SC::school<S>* sc::elem<_,_> 
 ensures  res::school<M> & M=union(S,{sc}) ;
{
 sc.next = SC; //null;
 return sc;
}

void insert(elem st, elem sc, ref elem ST, elem SC)
 requires ST::students<N,S> * st::elem<_,_> 
  //& intersect(N,{st})={} & intersect(S,{sc}) !={}
 ensures  ST'::students<M,S> & M=union(N,{st}) ;
{
  //st.attends = sc;
  //st.attends = null;
  st.next =ST;
  ST = st;
  assert false;
}
