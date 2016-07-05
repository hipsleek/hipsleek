pred_prim Thrd{-%P,+%Q}<>;
pred_prim Thrd2{+%Q@Split}<>;
pred_prim dead<>;


thrd create_thread(ref int nnn) 
  requires true
  ensures res::Thrd{-@full[nnn],+@full[nnn]& nnn'=nnn+1}<>;//'

/*

# ex60a.ss

HO-parameters has been reversed?

thrd create_thread(int@R n)[]
static EBase: [][](htrue) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; (res::Thrd{- (htrue) * (@full[n][] & true)( FLOW __norm),+ (emp) * (@full[n][] 
& n' = n+1)( FLOW __norm)}<>@M[HeapNode1]))) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 

static  EBase htrue&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [n]
                   res::Thrd{ + emp*N@full[n]&n'=1+n&{FLOW,(4,5)=__norm#E}[], - htrue*N@full[n]&{FLOW,(4,5)=__norm#E}[]}<>&
                   {FLOW,(4,5)=__norm#E}[]
*/

void forkk(thrd t)
  requires t::Thrd{-%P,+%Q}<> * %P
  ensures  t::Thrd2{+%Q}<>;

void joinkk(thrd t)
  requires t::Thrd2{+%Q}<>
  ensures %Q * t::dead<>;

int main(int x)
  requires @full[x] & x=5
  ensures res=6;
{
  dprint;
  // N@full[x]&MayLoop[] & x=5 & x'=x
  thrd t = create_thread(x);
  dprint;
/*
 State:t_39'::Thrd{-@full[x], +@full[x]&x'=1+x}<>
   *  N@full[t_39,x]& x=5&{FLOW,(4,5)=__norm#E}
*/
  x=x+2;
  /*
 State:t_39'::Thrd{ - htrue*N@full[x]&{FLOW,(4,5)=__norm#E}[], + emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_39,x]&x'=2+x_1380 & x=5&{FLOW,(4,5)=__norm#E}[]

 Why x'=2+x_1380?

  */

  dprint;
  forkk(t);
  dprint;
  joinkk(t);
  dprint;
  return 6;
}
/*
# ex60a.ss

# why first x=x+2 reflected as x'=2+x_1380?
# why "fork" cannot be used?
# why two Q in dprint3? should it be eliminated?
# how to handle parameters of forked tasks?

 State:t_39'::dead{}<>&x'=1+x & x'=2+x_1380 & x=5&{FLOW,(4,5)=__norm#E}[]
 
Do we need fork(f,x)?

dprint 1:
 State:t_39'::Thrd{ - htrue*N@full[x]&{FLOW,(4,5)=__norm#E}[], + emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_39,x]&x'=1+x_1378 & x=5&{FLOW,(4,5)=__norm#E}[]

dprint 2:
how to support with %P,%Q ?
 State:t_39'::Thrd2{ + emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_
39]@zero[x]&x=5 & x'=1+x_1378&{FLOW,(4,5)=__norm#E}[]
       es_ho_vars_map: [P --> htrue*N@full[x]&{FLOW,(4,5)=__norm#E}[]; 
                        Q --> emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]]


*/
