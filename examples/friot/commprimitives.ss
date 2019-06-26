/* hip_include 'msess/notes/node.ss' */
/**
============================= 1 ============================
*/

void ev (Channel ccc, int xxx)
  // requires ccc::Chan{@S emp}<>
  // ensures  ccc::Chan{@S ?v#v=xxx}<>;
  requires ccc::Chan{@S %R}<>
  ensures  ccc::Chan{@S %R;;?v#v=xxx}<>;
  
