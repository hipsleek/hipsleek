data LOCK {}

pred_prim Lock{+%P@Split}<>;
pred_prim Held{-%P@Split}<>;


void acq(LOCK l)
  requires l::Lock{+%P}<>@L * @Value[l]
  ensures  %P * l::Held{-%P}<>;

void release(LOCK l)
  requires l::Held{-%P}<> * %P  * @Value[l]
  ensures  emp;

LOCK create_latch(LOCK x) with %P
  requires x::LOCK<>
  ensures  res::Lock{+%P} & res=x;

void main()
 requires emp
  ensures emp;
{
int x=0;a=0;b=0;
 LOCK l= new LOCK();
 l=create_Lock(l) with @full[x]*@frac(1/2)[a,b] & x=a+b
// @zero[x]*@frac(1/2)[a,b]
 par {a@Frac(1/2),b@Frac(1/2),x@L} 
 case {@frac(1/2)[a],x@L} x::Lock{+ @full[x]*@frac(1/2)[a,b] & x=a+b}<>@L ->
     acq(x);
      x=x+1;
      a=1;
     rel(x);
   ||
 case {@frac(1/2)[b],x@L} x::Lock{+ @full[x]*@frac(1/2)[a,b] & x=a+b}<>@L->
     acq(x);
      x=x+1;
      b=1;
     rel(x);
}
