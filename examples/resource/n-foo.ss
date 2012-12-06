
pred_prim R<high:int>
  inv high>=0;

lemma "R split" self::R<b> & q,r>=0 & b=q+r <-> self::R<q> * self::R<r> ;

void checkR(R x, int n)
  requires x::R<a>@L & a>=n
  ensures true;

// subtract space from stack
void subR(R x, int n)
  requires x::R<a> & a>=n
  ensures x::R<a-n>;

// add back space into stack
void addR(R x, int n)
  requires x::R<a>
  ensures x::R<a+n>;

void f(R s) 
  requires s::R<m> & m=6
  ensures  s::R<m>;
{
  subR(s,2); //subtract stack frame
  dprint;
  g(s);
  addR(s,2); //add back stack frame prior to return
}

void g(R s) 
  requires s::R<m> & m=6 
  ensures  s::R<m>;
{
  subR(s,2); //subtract stack frame
  addR(s,2); //add back stack frame prior to return
}
