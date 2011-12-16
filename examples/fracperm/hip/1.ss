/* fork(id,method_name,single argument) */

class e1 extends __Exc{}

class thread extends __Exc{
  int id
}

void inc(ref int x)
requires true & flow __norm
ensures x'=x+1 & flow __norm; //'
{
  x++;
}


global int x;
global int y;
global int id;
global int id1;
global int id2;

void test()
requires true & flow __norm
  ensures eres::e1<> & x'=x+1 & flow e1; //'
{
  inc(x);
  raise new e1();
  dprint;
}

/* ================= */
/* ==== 1 thread === */
/* ================= */

void test()
requires true & flow __norm
ensures true & flow_norm
        and eres::thread<id> & x'=x+1 & flow thread; //'
{
  /* {id'=id & x'=x & flow __norm} */
  fork(id,inc,x);
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} */
}

void test1()
requires true & flow __norm
ensures x'=x+1 & flow __norm; //'
{
  /* {id'=id & x'=x & flow __norm} */
  fork(id,inc,x);
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} //' */
  join(id) // ?? how to figure out the thread<id>
  /* { We have to prove that: */
  /* // THREAD |- eres::thread<id> & (pure of id from the norm flow) */
  /*  eres::thread<id'> & id'=id & x'=x+1  
  /*  |- eres::thread<id'> & id'=id (VALID) * residue */
  /* } */
  /* //compose the residue with the norm flow */
  /* {id'=id & x'=x+1 & flow __norm} //' */
}

// fail
// example with a wrong thread id
void test1_1()
requires true & flow __norm
ensures x'=x+1 & flow __norm; //'
{
  /* {id'=id & id1'=id1 &x'=x & flow __norm} */
  fork(id,inc,x);
  /* {id'=id & id1'=id1 & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} //' */
  id=id1;
  /* {id'=id1' & id1'=id1 & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} //' */
  join(id) 
  /* {We have to prove: */
  /*   eres::thread<id'> & id'=id & x'=x+1  */
  /* |- eres::thread<id'> &id'=id1' & id1'=id1 (FAILED)} */

}

void test2(ref int x)
  requires true & flow __norm
  ensures 
    x<=0 & x'=x & flow __norm
    or (x>0 & flow __norm
        and eres::thread<id> & x'=x+1 & flow thread);  //'
{
  /* { id'=id & x'=x & flow __norm} */
  if(x>0){
    /* { id'=id & x'=x & x'>0 & flow __norm} */
    fork(id,inc,x);
    /* { id'=id & x'=x & x'>0 & flow __norm */
    /*   and eres::thread<id> & id'=id & x'=x+1 & flow thread} */
  }else
    /* { id'=id & x'=x & x'<=0 & flow __norm} */
  }
  /* { id'=id & x'=x & x'<=0 & flow __norm */
  /*   or (id'=id & x'=x & x'>0 & flow __norm */
  /*       and eres::thread<id> & id'=id & x'=x+1 & flow thread)} */
}

void test3(ref int x)
  requires true & flow __norm
  ensures 
    x<=0 & x'=x & flow __norm
    or (eres::e1() & x>0 & flow e1
        and eres::thread<id> & x'=x+1 & flow thread); 
{
  if(x>0){
    /* { id'=id & x'=x & x'>0 & flow __norm} */
    fork(id,inc,x);
    /* { id'=id & x'=x & x'>0 & flow __norm */
    /*   and eres::thread<id> & id'=id & x'=x+1 & flow thread} */
    raise new e1();
    /* { eres::e1() & id'=id & x'=x & x'>0 & flow e1 */
    /*   and eres::thread<id> & id'=id & x'=x+1 & flow thread} */
  }
  /* { id'=id & x'=x & x'<=0 & flow __norm} */
  /*   or (eres::e1() & id'=id & x'=x & x'>0 & flow e1 */
  /*      and eres::thread<id> & id'=id & x'=x+1 & flow thread)} */
}

void test4(ref int x)
  requires true & flow __norm
  ensures x'=x+1 & flow __norm; //'
{
  try{
    if(x>0){
      fork(id,inc,x);
      raise new e1();
    }
    /* { id'=id & x'=x & x'<=0 & flow __norm} */
    /*   or (eres::e1() & id'=id & x'=x & x'>0 & flow e1 */
    /*       and eres::thread<id> & id'=id & x'=x+1 & flow thread)} */
  }catch(e1 v){
    /* {(id'=id & x'=x & x'>0 & flow __norm */
    /*   and eres::thread<id> & id'=id & x'=x+1 & flow thread)} //' */
    join(id);
    /* {id'=id & x'=x+1 & x>0 & flow __norm} //' */
  }
}

void test5(ref int x)
  requires true & flow __norm
  ensures x'=x+1 & flow __norm; //'
  ensures
    x<=0 & x'=x & flow __norm
    or x>0 & x'=x+1 & flow __norm;
{
  if(x>0){
    fork(id,inc,x);
  }else{
  }
  /* { id'=id & x'=x & x'<=0 & flow __norm */
  /*   or (id'=id & x'=x & x'>0 & flow __norm */
  /*       and eres::thread<id> & id'=id & x'=x+1 & flow thread)} */
  if (x>0){
    /* { (id'=id & x'=x & x'>0 & flow __norm */
    /*    and eres::thread<id> & id'=id & x'=x+1 & flow thread)} //' */
    join(id);
    /* { id'=id & x'=x+1 & x>0 & flow __norm } //' */
  }else{
    /* { id'=id & x'=x & x'<=0 & flow __norm} //' */
  }
  /* { id'=id & x'=x & x'<=0 & flow __norm} //' */
  /*   or id'=id & x'=x+1 & x>0 & flow __norm} //' */
}

/* ================= */
/* ==== 2 thread === */
/* ================= */
void test11(int ref x, int ref y)
requires true & flow __norm
ensures x'=x+1 & y'=y+1 & flow __norm; //'
{
  /* {id1'=id1 & id2'=id2 & x'=x & y'=y & flow __norm} */
  fork(id1,inc,x);
  /* {id1'=id1 & id1'=id1 & x'=x & y'=y & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread} */
  fork(id2,inc,y);
  /* {id1'=id1 & id2'=id2 & x'=x & y'=y & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=y+1 & flow thread} */
  join(id1);
  /* { (1) eres::thread<id1'> & id1'=id1 & x'=x+1  */
  /*   and eres::thread<id2'> & id2'=id2 & y'=y+1 & flow thread} */
  /*     |- eres::thread<id1'> & id1'=id1 (VALID) => merge */
  /*    (2) eres::thread<id2'> & id2'=id2 & y'=y+1  */
  /*        and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*        |- eres::thread<id1'> & id1'=id1 (FAIL) } */
  /* {id1'=id1 & id2'=id2 & x'=x+1 & y'=y & flow __norm */
  /*   and eres::thread<id2'> & id2'=id2 & y'=y+1 & flow thread} */
  join(id2);
  /* {id1'=id1 & id2'=id2 & x'=x+1 & y'=y+1 & flow __norm} */
}

void test21(ref int x, ref int y)
  requires true & flow __norm
  ensures 
    (x>0 & flow __norm
     and eres::thread<id1> & x'=x+1 & flow thread)
    or (x<=0 & flow __norm
       and eres::thread<id2> & y'=y+1 & flow thread); 
{
  if(x>0){
    fork(id1,inc,x);
  }else{
    fork(id2,inc,y);
  }
}

void test31(ref int x)
  requires true & flow __norm
  ensures
    x<=0 & x'=x & flow __norm
    or (eres::e1() & x>0 & flow e1
        and eres::thread<id1> & x'=x+1 & flow thread
        and eres::thread<id2> & y'=y+1 & flow thread); 
{
  if(x>0){
    fork(id1,inc,x);
    fork(id2,inc,y);
    raise new e1();
  }
}

void test41(ref int x, ref int y)
  requires true & flow __norm
  ensures x'=x+1 & flow __norm
          and eres::thread<id2> & y'=y+1 & flow thread; //'
{
  try{
    if(x>0){
      fork(id1,inc,x);
      fork(id2,inc,y);
      raise new e1();
    }
  }catch(e1 v){
    join(id1);
  }
}


/*tricky examples*/
void test_hard(int ref x, int ref y)
requires true & flow __norm
ensures y'=y+1 & flow __norm
        and eres::thread<id1> & x'=x+1 & flow thread; //'
{
  /* {x'=x & y'=y & id1'=id1 & id2'=id2 & flow __norm} */
  fork(id1,inc,x);
  /* {x'=x & y'=y & id1'=id1 & id2'=id2 & flow __norm */
  /*  and eres::thread<id1'> & id1'=i1d & x'=x+1 & flow thread} //' */
  // We need pure constraints id1'=id1
  fork(id2,inc,y);
  /* {x'=x & y'=y & id1'=id1 & id2'=id2 & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=x+1 & flow thread} //' */
  //swap id1 and id2
  int id3;
  /* {id3'=0 & x'=x & y'=y & id1'=id1 & id2'=id2 & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=x+1 & flow thread} //' */
  id3=id1;
  /* {id3'=id1' & x'=x & y'=y & id1'=id1 & id2'=id2 & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=x+1 & flow thread} //' */
  id1=id2;
  /* {id3'=id1 & x'=x & y'=y & id1'=id2' & id2'=id2 & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=x+1 & flow thread} //' */
  id2=id3;
  /* {id3'=id1 & x'=x & y'=y & id1'=id2 & id2'=id3' & flow __norm */
  /*  and eres::thread<id1'> & id1'=id1 & x'=x+1 & flow thread */
  /*  and eres::thread<id2'> & id2'=id2 & y'=x+1 & flow thread} //' */
  join(id1); // inc(y) | id1'=id2 => join(id2)
  /* we need to prove */
  /* one of the two thread flows |- eres::thread<id1'> & id1'=id2 * residue */
 /* then compose the residue with the norm flow */

}
