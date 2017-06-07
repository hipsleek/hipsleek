pred_prim security<i : int>;

bool eqv(int a, int b)
  requires a::security<A>@L & b::security<B>@L
  case {
    a = b -> ensures res::security<R> & res & R = max(A, B);
    a != b -> ensures res::security<R> & !res & R = max(A, B);
  }

bool eqv2(int a, int b)
  requires a::security<A>@L * b::security<B>@L
  case {
    a = b -> ensures res::security<R> & res & R = max(A, B);
    a != b -> ensures res::security<R> & !res & R = max(A, B);
  }

// Should pass
bool least_upper_bound1 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 1;
{
  bool x = eqv(p, q);
  return x;
}

// Should pass
/***
 * Generated entailments:
 *  checkentail p::security<P>@M * q::security<Q>@M&Q<=0 & P<=1 & q'=q & p'=p & MayLoop[]&{FLOW,(4,5)=__norm#E}[] |- q'::security<A>@L&{FLOW,(4,5)=__norm#E}[].
 *  res:  1[
 *    p::security<P>@M * (Hole[1883])&Q<=0 & P<=1 & q'=q & p'=p & A=Q&
 *      {FLOW,(4,5)=__norm#E}[]
 *      es_gen_impl_vars(E): [B]
 *   ]
 *  checkentail p::security<P>@M * q::security<Q>@M&Q<=0 & P<=1 & q'=q & p'=p & A=Q & MayLoop[]&{FLOW,(4,5)=__norm#E}[] |- q'::security<B>@L&{FLOW,(4,5)=__norm#E}[].
 *  res:  1[
 *    p::security<P>@M * (Hole[1884])&Q<=0 & P<=1 & q'=q & p'=p & A=Q & B=Q&
 *      {FLOW,(4,5)=__norm#E}[]
 *      es_gen_impl_vars(E): []
 *    ]
 */
bool least_upper_bound2 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  bool x = eqv(q, q);
  return x;
}

// Should pass
bool least_upper_bound3 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 1;
{
  bool x = eqv2(p, q);
  return x;
}

// Should fail
/***
 * Generated entailments:
 *  checkentail p::security<P>@M * q::security<Q>@M&Q<=0 & P<=1 & q'=q & p'=p & MayLoop[]&{FLOW,(4,5)=__norm#E}[] |-  q'::security<A>@L * q'::security<B>@L&{FLOW,(4,5)=__norm#E}[].
 *  res:  failctxfe_kind: MAY
 *       fe_name: separation entailment
 *       fe_locs: {
 *   fc_message: do_unmatched_rhs : q'::security<B>@L(may)
 *   fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}
 *  }
 *  [[ SEARCH ==>  Match(q,q') ==>  SEARCH ==>  COND ==>  UnmatchedRHSData]]false
 */
bool least_upper_bound4 (int p, int q)
  requires p::security<P> * q::security<Q> & P <= 1 & Q <= 0
  ensures res::security<R> & R <= 0;
{
  bool x = eqv2(q, q);
  return x;
}
