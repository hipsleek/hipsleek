/*
  [nonworking example]

  Inspired by example at verifast-12.3/examples/incr.c
  
  NOTE: need a way to control automatic split/combine of both cell and lock

 */

data lock{}

data intCell{
  int val;
}

data counter{
  lock l; 
  intCell count;
  intCell oldCount;
}

lemma "splitCell" self::intCell(f)<v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::intCell(f1)<v> * self::intCell(f2)<v> & 0.0<f<=1.0;

/* lemma "combineCell" self::intCell(f1)<v> * self::cell(f2)<l,v> -> self::cell(f1+f2)<l,v>; */

lemma "splitLock" self::LOCK(f)<x,c> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x,c> * self::LOCK(f2)<x,c> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<x,c> * self::LOCK(f2)<x,c> -> self::LOCK(f1+f2)<x,c>;


LOCK<x,oldCount> == self::lock<>
  inv self!=null
  inv_lock x::counter<self,count,oldCount> * count::intCell<v> * oldCount::intCell(1/2)<oldV> & v>=oldV;

void main()
  requires ls={}
  ensures ls'={}; //'
{
  lock l = new lock();
  intCell countC = new intCell(0);
  intCell oldCountC = new intCell(0);
  counter x = new counter(l,countC,oldCountC);
  //print;
  init[LOCK](l,x,oldCountC);

  release[LOCK](l,x,oldCountC);
  dprint;
  int id;
  id = fork(incrementor,l,x,oldCountC); // there is an automatic split here
  dprint;
  int oldC=0;

  /* while(true) */
  /*   requires l::LOCK(1/2)<x,oldCountC> * oldCountC::intCell(1/2)<oldC> & ls={} */
  /* ensures l::LOCK(1/2)<x,oldCountC> * oldCountC::intCell(1/2)<oldC> & ls'={}; //' */
  /* { */
    acquire[LOCK](l,x,oldCountC);
    /* dprint; */
    int count = x.count.val;
    int old = oldCountC.val;
    assert count'>=old';
    /* oldC = count; */
    /* x.oldCount.val = count; */
    /* dprint; */
    release[LOCK](l,x,oldCountC);
    dprint;
  /* } */
}

//valid
void incrementor(lock l,counter x,intCell oldCount)
  requires l::LOCK(1/2)<x,oldCount> & ls={}
  ensures l::LOCK(1/2)<x,oldCount> & ls'={}; //'
/* { */
/*   while (true) */
/*     requires l::LOCK(1/2)<x,oldCount> & ls={} */
/*   ensures l::LOCK(1/2)<x,oldCount> & ls'={}; //' */
/*   { */
/*     acquire[LOCK](l,x,oldCount); */
/*     dprint; */
/*     x.count.val++; */
/*     release[LOCK](l,x,oldCount); */
/*   } */
/* } */
