data Transition {
  int timing;
  Transition next;
}

data Signal {
  bool initialValue;
  Transition transitions;
}

ll_trans<n> == self = null & n = 0 or
  self::Transition<_, p> * p::ll_trans<n - 1>
  inv n >= 0;

Signal invert(Signal s) 
  requires s::Signal<init, trans> * trans::ll_trans<n> & Term[0]
  ensures res::Signal<inv_init, trans> * s::Signal<init, trans> * trans::ll_trans<n> & 
          (init & !inv_init | !init & inv_init);
{
  return new Signal(!s.initialValue, s.transitions);
}

bool valueAt(Signal s, int t) 
  requires s::Signal<init, trans> * trans::ll_trans<n> & Term
  ensures s::Signal<init, trans> * trans::ll_trans<n>;
{
  bool v = s.initialValue;
  Transition trans = s.transitions;
  return valueAt_l(v, t, trans);
}

bool valueAt_l(bool v, int t, Transition trans)
  requires trans::ll_trans<n> & Term[n]
  ensures trans::ll_trans<n>;
{
  if (trans == null) return v;
  else {
    if (t < trans.timing)
      return v;
    return valueAt_l(!v, t, trans.next);
  }
}

void printSignal(Signal s) 
  requires s::Signal<init, t> * t::ll_trans<n> & Term[1]
  ensures s::Signal<init, t> * t::ll_trans<n>;
{
  bool v = s.initialValue;
  Transition trans = s.transitions;
  while (trans != null) 
    requires trans::ll_trans<n> & Term[0, n]
    ensures trans::ll_trans<n> & trans' = null;
  {
	  v = !v;
    trans = trans.next;
  }
}

Transition shiftTrans(Transition t, int delta) 
  requires t::ll_trans<n> & Term[0, n]
  ensures res::ll_trans<n> * t::ll_trans<n>;
{
  if (t == null) return null;
  else
    return new Transition(t.timing + delta, shiftTrans(t.next, delta));
}

Signal shift(Signal s, int delta) 
  requires s::Signal<init, trans> * trans::ll_trans<n> & Term[1]
  ensures res::Signal<init, trans_r> * trans_r::ll_trans<n> * 
          s::Signal<init, trans> * trans::ll_trans<n>;
{
  return new Signal(s.initialValue, shiftTrans(s.transitions, delta));
}

bool isWellFormedTrans(Transition t) 
  requires t::ll_trans<n> & Term[n]
  ensures t::ll_trans<n>;
{
  if (t == null) return true;
  else if (t.next == null) return true;
  else return (t.timing < t.next.timing) && isWellFormedTrans(t.next);
}

bool isWellFormed(Signal s) 
  requires s::Signal<init, trans> * trans::ll_trans<n> & Term
  ensures s::Signal<init, trans> * trans::ll_trans<n>;
{
  return isWellFormedTrans(s.transitions);
}

Transition copyTrans(Transition t)
  requires t::ll_trans<n> & Term[0, n]
  ensures t::ll_trans<n> * res::ll_trans<n>;
{
  if (t == null) return null;
  else {
    return new Transition(t.timing, copyTrans(t.next));
  }
}

Transition xorTransitions(Transition t1, Transition t2) 
  requires t1::ll_trans<n1> * t2::ll_trans<n2> & Term[1, n1 + n2]
  ensures t1::ll_trans<n1> * t2::ll_trans<n2> * res::ll_trans<_>;
  
  requires t1::ll_trans<n1> & t1 = t2 & Term[n1]
  ensures t1::ll_trans<n1> * res::ll_trans<_> & t1 = t2;
{
  if (t1 == null) return copyTrans(t2);
  else if (t2 == null) return copyTrans(t1);
  else {
    int tt1 = t1.timing;
    int tt2 = t2.timing;
    if (tt1 < tt2)
      return new Transition(tt1, xorTransitions(t1.next, t2));
    else if (tt2 < tt1)
      return new Transition(tt2, xorTransitions(t1, t2.next));
    else
      return xorTransitions(t1.next, t2.next);
  }
}

Signal xorSignals(Signal s1, Signal s2) 
  requires s1::Signal<i1, t1> * t1::ll_trans<n1> * s2::Signal<i2, t2> * t2::ll_trans<n2> & Term[2]
  ensures res::Signal<i, t> * t::ll_trans<_> * 
          s1::Signal<i1, t1> * t1::ll_trans<n1> * 
          s2::Signal<i2, t2> * t2::ll_trans<n2> & 
          (i1 != i2 & i | i1 = i2 & !i);
  
  requires s1::Signal<i1, t> * s2::Signal<i2, t> * t::ll_trans<n2> & Term[2]
  ensures res::Signal<i, tr> * tr::ll_trans<_> * 
          s1::Signal<i1, t> * s2::Signal<i2, t> * t::ll_trans<n2> & 
          (i1 != i2 & i | i1 = i2 & !i);
{
  return new Signal(
    (s1.initialValue) != (s2.initialValue),
    xorTransitions(s1.transitions, s2.transitions));
}

bool recValueAtTrans(bool value, Transition t, int timing) 
  requires t::ll_trans<n> & Term[n]
  ensures t::ll_trans<n>;
{
  if (t == null) return value;
  else if (timing < t.timing) return value;
  else return recValueAtTrans(!value, t.next, timing);
}

bool recValueAt(Signal s, int instant) 
  requires s::Signal<init, trans> * trans::ll_trans<n> & Term
  ensures s::Signal<init, trans> * trans::ll_trans<n>;
{
  return recValueAtTrans(s.initialValue, s.transitions, instant);
}

Signal renverser(Signal s) 
  requires s::Signal<init, t> * t::ll_trans<n> & Term[1]
  ensures res::Signal<_, t2> * t2::ll_trans<n> * 
          s::Signal<init, t> * t::ll_trans<n>; 
{
  bool v = s.initialValue;
  Transition t = s.transitions;
  Transition t2 = null;
  while (t != null) 
    requires t::ll_trans<n1> * t2::ll_trans<n2> & Term[0, n1]
    ensures t::ll_trans<n1> * t2'::ll_trans<n1 + n2> & t' = null;
  {
    t2 = new Transition(-t.timing, t2);
    v = !v;
    t = t.next;
  }
  return new Signal(v, t2);
}

void testValues(Signal s) 
  requires s::Signal<init, t> & Term
  ensures s::Signal<init, t>;  

void test(Signal s) 
  requires s::Signal<init, t> * t::ll_trans<n> & Term
  ensures s::Signal<init, t> * t::ll_trans<n>;
{
    printSignal(s);
    testValues(s);
}

void testAll(Signal s) 
  requires s::Signal<init, t> * t::ll_trans<n> & Term[3]
  ensures s::Signal<init, t> * t::ll_trans<n>;
{
  test(s);
  Signal is = invert(s);
  test(is);
  //System.out.println("XOR");
  printSignal(xorSignals(s, is));
  //System.out.println();
  Signal it = shift(is, 1);
  test(it);
  //System.out.println("XOR");
  printSignal(xorSignals(it, is));
  //System.out.println();
  Signal ir = renverser(it);
  test(ir);
}
/*
int random() 
  requires Term
  ensures true;
  
void main()
  requires Term
  ensures true;
{
  Signal s1 = new Signal(false, null);
  Signal s2 = new Signal(false, new Transition(10*random(), 
					                      new Transition(50*random(), null)));
  Signal s3 = new Signal(true,  new Transition(10*random(), 
                                new Transition(15*random(),
                                new Transition(30*random(), null))));
  Signal signal1 = new Signal(false, new Transition(1*random(), 
                                     new Transition(3*random(), 
                                     new Transition(4*random(), null))));
  //System.out.println("\ns1");
  testAll(s1);
  //System.out.println("\ns2");
  testAll(s2);
  //System.out.println("\ns3");
  testAll(s3);
      
  //System.out.println("s2 ^ s3");
  printSignal(xorSignals(s2, s3));
      
  //System.out.println("\nsigna1");
  testAll(signal1);
}
*/
  
  
  
  
