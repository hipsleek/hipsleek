/*
  example proving deadlock freedom using disjunctive delayed formulae

*/

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

/**/

void func(bool b, lock l1,lock l2)
  requires l1::LOCK(0.6)<> & l1 notin LS & b
     or l2::LOCK(0.6)<> & l2 notin LS & !b
  ensures LS'=LS; //'
{
  int i;
  if (b){
    acquire[LOCK](l1);
    release[LOCK](l1);
  }else{
    acquire[LOCK](l2);
    release[LOCK](l2);
  }
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
   lock l1 = new lock();
   init[LOCK](l1);
   release[LOCK](l1);
   lock l2 = new lock();
   init[LOCK](l2);
   release[LOCK](l2);
   bool b = true;
   //LS={}
   int id = fork(func,b,l1,l2);
   //DELAYED: l1 notin LS & b | l2 notin LS & !b

   //LS={}
   acquire[LOCK](l2);
   //LS={l2} & b

   join(id); //CHECK,ok because LS={l2} & b |- l1 notin LS & b

   release[LOCK](l2);

   dprint;
}
