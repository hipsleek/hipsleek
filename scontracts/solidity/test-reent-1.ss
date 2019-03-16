hip_include 'scontracts/mapprimitives.ss'

/* data structures for the special variables */
data message{
       int data_;
       int gas;
       address sender;
       int sig;
       int value;
       }

data address {
     int id;
}

global message msg;
global int bal;

void call(address userid, int arg)
   requires  arg>0
   ensures   bal'=bal-arg;

void foo()
  infer [@reentrancy]
  requires msg::message<_,_,id,_,_>@L & bal>0
  ensures  bal'=0;
{
 if(bal>0){
    call(msg.sender,bal);
    bal = 0;
 }
}


void goo()
  infer [@reentrancy]
  requires msg::message<_,_,_,_,_>@L & bal>0
  ensures  bal'=0;
{
 if(bal>0){
    bal = 0;
    call(msg.sender,bal);
 }
}
