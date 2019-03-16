

// contract K

void foo()
   requires true
   ensures  bal=0 & money' = money-bal;
{
  if (bal>0)
     { call(_,bal); // at this point no call to a
                    // method which alters the global state
       // invariant bal'=bal
       bal=0;
     }
}

/*
1. check that no precondition holds
(where the corresponding post highlights a change in the state)

2. check that all the preconditions create a contra with the callee state
(where the corresponding post highlights a change in the state)

3. have an invariant
*/

void goo()
{
 if (bal>0)
    { send(msg.sender,bal);
      bal = 0;
    }
}


// contract M

void fallback(){
  K.goo();
}

void main(){
  K.foo();
}
