
/* //BUG */
/* void test() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x; */
/*   bool b=true; */
/*   try{ */
/*     if (b){ */
/*       x = new int_ptr(7); */
/*       return; */
/*     } */
/*   }catch(__norm e){ */
/*     delete(x); */
/*     //int z; */
/*   }; */
/* } */


/* //BUG */
/* void test() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x; */
/*   try{ */
/*      x = new int_ptr(7); */
/*   }catch(__norm e){ */
/*     //delete(x); */
/*     int z; */
/*   }finally{ */
/*     int y; // ERROR due to empty flow_store */
/*   }; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int x=7; */
/*   x=x+1; */
/*   int y=1; */
/*   int* p1=&x; */
/*   int* p2=&y; */
/*   *(p1) = (*p1) + (*p2); */
/*   int z =x; */
/*   assert(z'=9); */
/* } */

/* void main_new() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x = new int_ptr(7); */
/*   try{ */
/*     x.val=x.val+1; */
/*     int_ptr y = new int_ptr(1); */
/*     try{ */
/*       int_ptr p1=x; */
/*       int_ptr p2=y; */
/*       p1.val = p1.val + p2.val; */
/*       int z =x.val; */
/*       assert(z'=9); */
/*     }catch(__norm e){ */
/*       delete(y); */
/*     }; */
/*   }catch(__norm e){ */
/*     delete(x); */
/*   }; */
/* } */

/* void test(bool b) */
/*   requires true */
/*   ensures true; */
/* { */
/*   int*p; */
/*   if (b){ */
/*     int y = 8; */
/*     p=&y; */
/*     return; */
/*   } */
/*   int x = 1; */
/*   dprint; */
/* } */

void test_new(bool b)
  requires true
  ensures true;
{
  int_ptr p;
  if (b){
    int_ptr y = new int_ptr(8);
    try{
      p=y;
      return;
      //dprint;
    }catch(__cflow e){
      //translate all caught flows into norm flow -> lost orig flow info
      //dprint;
      delete(y);
      //dprint;
      raise e;//at this point, we just know __cflow. We lose the
      // original flow info
    };
  }
  //dprint;
  int x = 1;
}

/* void test2(bool b) */
/*   requires true */
/*   ensures true; */
/* { */
/*   int* p; */
/*   if (b){ */
/*     int y=7; */
/*     p=&y; */
/*     return; */
/*   } */
/*   return; */
/*   dprint; */
/* } */
