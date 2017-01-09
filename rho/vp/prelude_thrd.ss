pred_prim Thrd{-%P,+%Q}<>;
pred_prim Thrd2{+%Q@Split}<>;
pred_prim dead<>;


thrd create_thread(int n) 
                    with %P
    requires emp
  ensures res::Thrd{-%P,+%P}<>;

void fork(thrd t)
  requires t::Thrd{-%P,+%P}<> * %P
  ensures  t::Thrd2{+%P}<>;

void join(thrd t)
  requires t::Thrd2{+Q}<>
  ensures %Q * t::dead<>;
