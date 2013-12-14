// inline fields

data pair {
	int x;
	int y;
}
data quad {
	inline pair p1;
	pair p2;
}
data quad__star {
  quad deref;
}

/*
    
 */
int foo(quad val_q)
  requires val_q::quad<a,b,p>@L
  ensures res=a;
{
  quad tmp = val_q;
  val_q=null;
  return tmp.p1.x;
}


int foo3(quad val_q)
/*@
  requires val_q::quad<a,b,p>@L
  ensures res=a;
*/
{
  quad__star p = new quad__star(null);
  p.deref=val_q;
  //quad* p=q;
  return val_q.p1.x;
}

void main()
 requires true
  ensures true;
{
  quad__star p = new quad__star(null); //stack alloc
  p.deref = new quad(0,0,null); // malloc
  // *&p ==> p
  // foo(p) ==> foo(*p) // pass-by-ptr
  // foo(&p) ==> foo(*&p) ==> foo(p) // pass-by-ptr
  assert(p'!=null);//'
  int x=foo(p.deref);
  dprint;
  assert(p'!=null);//'
}
int goo(quad q)
  requires q::quad<a,b,p>
  ensures q::quad<a,b,p> & res=b;
{
  return q.p1.y;
}

int hoo(quad q)
  requires q::quad<a,b,p> * p::pair<c,d>
  ensures q::quad<a,b,p> * p::pair<c,d> & res=d;
{
  return q.p2.y;
}

int too(quad q)
  requires q.quad.p1.y::<b>
  ensures q.quad.p1.y::<b> & res=b;
{
  return q.p1.y;
}

int noo(quad q)
  requires q::quad<#,b,#>
  ensures q.quad.p1.y::<b> & res=b;
{
  return q.p1.y;
}

int roo(quad q)
  requires q::quad<#,b,#>
  ensures q::quad<a@A,b,#> & res=b;
{
  return q.p1.y;
}

