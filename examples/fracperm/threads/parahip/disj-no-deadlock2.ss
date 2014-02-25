/*
  example proving deadlock freedom using both
  disjunctive formulae and disjunctive delayed formulae
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

/**/

void func(bool b, lock l1,lock l2)
 case {
  b -> requires l1::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS] & b 
       ensures LS'=LS;
  !b -> requires l2::LOCK(0.6)<> & [waitlevel<l2.mu # l2 notin LS] & !b 
       ensures LS'=LS;
  }

  /* requires l1::LOCK(0.6)<> & l1 notin LS & b &l1!=l2 */
  /*    or l2::LOCK(0.6)<> & l2 notin LS & !b &l1!=l2 */
  /* ensures LS'=LS; //' */
{
  int i;
  
  if (b){
    acquire(l1);
    release(l1);
  }else{
    acquire(l2);
    release(l2);
  }
  
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
   lock l1 = new lock();
   init[LOCK](l1); //initialize l1 with invariant LOCK
   release(l1);
   //
   lock l2 = new lock();
   init[LOCK](l2);
   release(l2);

   bool b; //b got unknown value
   
   //LS-{}
   int id = fork(func,b,l1,l2);
   //DELAYED: l1 notin LS & b | l2 notin LS & !b
   

   if (b){
     //LS={}
     acquire(l2);
     //LS={l1}
   }else{
     //LS={}
     acquire(l1);
     //LS={l2}
   }
   
   // LS={l2} & b | LS={l1} & !b
   join(id); //CHECK, no deadlock
   // LS={l2} & b | LS={l1} & !b

   if (b){
     //LS={l2}
     release(l2);
     //LS={}
   }else{
     //LS={l1}
     release(l1);
     //LS={}
   }
   
}
