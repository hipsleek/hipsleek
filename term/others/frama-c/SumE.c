#pragma JessieIntegerModel(math)
#pragma JessieTerminationPolicy(user)

/*@ terminates x >= 0 && x % 2 == 0; // Frama-C with Jessie or WP plugin ignores this specification

    behavior even:
      assumes x >= 0 && x % 2 == 0;
      //terminates true; // [kernel] user error: wrong order of clause in contract: terminates after behavior.
      //decreases x; // "[kernel] user error: wrong order of clause in contract: decreases after behavior"
      ensures \result % 2 == 0;
      
    behavior odd:
      assumes x >= 0 && x % 2 == 1;
      ensures \false;
    
    behavior neg:
      assumes x < 0;
      ensures \false;
    
    complete behaviors even, odd, neg;
    disjoint behaviors even, odd, neg;
  @*/
int sumE(int x)
{
  if (x == 0) 
    return 0;
  else
    return x + sumE(x - 2);
}


