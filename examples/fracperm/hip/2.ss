
//one thread (fork/join)
void test1()
requires true & flow __norm
ensures x'=x+1 & flow __norm; //'
{
  /* {id'=id & x'=x & flow __norm} */
  fork(id,inc,x);
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} //' */
  join(id);
  /* { We have to prove that: */
  /* // THREAD |- eres::thread<id> & (pure of id from the norm flow) */
  /*  eres::thread<id'> & id'=id & x'=x+1  
  /*  |- eres::thread<id'> & id'=id (VALID) * residue */
  /* } */
  /* //compose the residue with the norm flow */
  /* {id'=id & x'=x+1 & flow __norm} //' */
}

// fork only + raise
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


// one thread (fork/join) + try/catch
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

//2 thread (fork/join)
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
