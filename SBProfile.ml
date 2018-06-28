type stats_entail = {
  sent_time_unify_heap : float;
  sent_time_simplify : float;
  sent_time_choose_hypo : float;
  sent_time_choose_theorem : float;
  sent_time_check_sat : float;
  sent_time_check_imply : float;
}


let mk_stats_entail () =
  { sent_time_unify_heap = 0.;
    sent_time_simplify = 0.;
    sent_time_choose_hypo = 0.;
    sent_time_choose_theorem = 0.;
    sent_time_check_sat = 0.;
    sent_time_check_imply = 0.; }
