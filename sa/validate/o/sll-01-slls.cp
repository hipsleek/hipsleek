
helper:SUCCESS[
ass [H][]:{
  // POST (1;0)
   emp& res=null --> H(res);
 // POST (2;0)
   H(tmp_1111) * res::node_top<tmp_1111,l_1101>@M& l_1101=null --> H(res);
 // POST (2;0)
   H(tmp_1113) * l_1107::node_low<flted_35_1105>@M * res::node_top<tmp_1113,l_1107>@M&flted_35_1105=null --> H(res)
 }

hpdefs [H][]:{
   H(res_1114) <-> emp&res_1114=null
    or H(tmp_1111) * res_1114::node_top<tmp_1111,l_1101>@M&l_1101=null
    or H(tmp_1113) * l_1107::node_low<flted_35_1105>@M *
      res_1114::node_top<tmp_1113,l_1107>@M&flted_35_1105=null
 }
]