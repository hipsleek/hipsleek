/* hip_include 'msess/notes/node.ss' */
/**

============================= 1 ============================
Send/Receive where the means for transmission are channels:
each two roles/process who are communicating with each other
do so by using an exclusive channel

*/

/**
 int
*/
void send (Channel ccc, int xxx)
  requires ccc::Chan{@S !v#%L(v);;%R}<> * %L(xxx)
  ensures  ccc::Chan{@S %R}<>;

int receive (Channel ccc)
  requires ccc::Chan{@S ?v#%L(v);;%R}<>
  ensures  ccc::Chan{@S %R}<> * %L(res);



/**
 Channel
*/
void sendc (Channel c, Channel x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

Channel receivec (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);

/**
   Addr
*/
void senda (Channel c, Addr x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

Addr receivea (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);


/**
   Date
*/
void sendd (Channel c, DDate x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

DDate received (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);

/**
   String
*/
void sends (Channel c, SString x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

SString receives (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);
  
/**

============================= 2 ============================
OPEN/CLOSE
*/

/* 
   cl  - logical channel
   res - program channel
*/
Channel open() with (cl,P,GGG) 
  requires cl::INIT<GGG>
  ensures  cl::OPENED<cl,P,GGG,res>;

/* 
   cl - logical channel
   c  - program channel
*/
void close(Channel c)
  requires c::EMPTY<cl,c,G>
  ensures  true;


/**

============================= 3 ============================
Explicit Synchronization Mechanisms
*/

void notifyAll(cond w)
  requires w::NOTIFY{ w::Guard{ %P }<>}<> * %P
  ensures  w::NOTIFY{ %P}<> ;

/* perhaps split formula in 2 (non-not, not). solve the non-not and w its residue solve not if fail -> succeed, succeed - >fail */
void wait(cond w)
/* infer [] */
  requires w::WAIT{ %P, %R}<>  * w::NOT{ %P}<>
  ensures  w::WAIT{ %P, emp}<> * %R ;



/* lemma NOT{%R} * %R <- false. */

/* lemma_norm self::SNOT{%P}<> * %P <- false. */
/* lemma_norm !(%P) <- self::SNOT{%P}<>       */
