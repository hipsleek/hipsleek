/*

  Description: fairly complicated inter-procedural passing 
  of stack variables between concurrent threads

 */
pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

void inc(ref int i)
 requires @full[i]
 ensures  @full[i] & i'=i+1; //' &
{
  i++;
}

Thrd fork_inc(ref int i)
  requires @full[i]
  ensures  res::Thrd{+@full[i] & i'=i+1}<>; //' &

Thrd creator(ref int x,ref int y)
  requires @full[x,y]
  ensures res::Thrd{+ @full[x] & x'=x+1}<> * @full[y] & y'=y+1 ; //& x'=x;
{
  Thrd id;
  id=fork_inc(x);
  x=x+1;
  inc(y);
  return id;
}

void joiner(Thrd id, ref int x)
  //requires id::Thrd{+ @full[x] & x'=x+1}<> * @value[id]
  //ensures  id::dead<> * @full[x] & x'=x+1 ; //' @full[x] &
  //requires id::Thrd{+ @full[x] }<> * @value[id]
  //ensures  id::dead<> * @full[x] & x'=0; //' @full[x] &
  requires id::Thrd{+  @full[x] * %PP(x')}<> * @value[id] 
  // x' in pre? %%PP(x')
  // also %%PP(x')
  ensures  (exists x0: id::dead<> * @full[x] * %PP(x0) & x'=x0+1); //' @full[x] &
{
  join2(id);
  x=x+1;
  dprint;
}


int main()
requires true
  ensures res=1;
{
  Thrd id;
  int xxx,y;
  xxx=0;y=0;
  // @full[id_38,xxx_39,y_40]&y_40'=0 & xxx_39'=0
  //dprint;
  id = creator(xxx,y);
  // id_38'::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39[]}<>*U@full[id_38,y_40]@zero[xxx_39]&y_40'=1+0 & xxx_39'=0
  dprint;
  // (exists xxx_1415: (htrue) * id_35'::Thrd{U@full[xxx_36]&xxx_36'=1+xxx_1415
  // &{FLOW,(4,5)=__norm#E}[]}<>*U@full[id_35,y_37]@zero[xxx_36]&y_37'=1+0 & xxx_1415=0
  joiner(id,xxx);
  // (htrue) * id_35'::Thrd{ + emp*N@zero[xxx_36]&{FLOW,(4,5)=__norm#E}[]}<> * id_35'::dead{}<>*
  // U@full[id_35,xxx_36,y_37]&xxx_36'=0 & xxx_1422=0 & y_37'=1+0&{FLOW,(4,5)=__norm#E}[]
  // where is xxx_36'=1+xxx_141 ??
  dprint; 
  return xxx+y;
}


/*
# ex37c-ho_task_decompose.ss --ann-vp -p main -dre "subst.*pre"


id_35'::Thrd{ + emp*U@full[xxx_36]&xxx_36'=1+xxx_1438&{FLOW,(4,5)=__norm#E}[]}<>
 *U@full[id_35,y_37]@zero[xxx_36]&xxx_1438=0 & y_37'=1+0& {FLOW,(4,5)=__norm#E}[]
  |-  id_35'::Thrd{ + emp*U@full[xxx_36]&xxx_36'=1+xxx_36&{FLOW,(4,5)=__norm#E}[]}<>
      * U@value[id_35]&{FLOW,(4,5)=__norm#E}[]. 



x --> x' must not go into higher-order component..

why pre had problem below?

 |-  id_38'::Thrd{ + emp*U@full[x_39']&x_39'=1+x_39'
           &{FLOW,(4,5)=__norm#E}[]}<>*


# creation
subst_struc_pre@1
subst_struc_pre inp1 :[(xxx_39,xxx_39'),(y_40,y_40'),(LS,LS'),(LSMU,LSMU'),(waitlevel,waitlevel')]
subst_struc_pre inp2 : EBase emp*U@full[xxx_39,y_40]&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [xxx_39;y_40]
 res::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39&{FLOW,(4,5)=__norm#E}[]}<>*
 U@full[y_40]&y_40'=1+y_40&{FLOW,(4,5)=__norm#E}[]
                   
subst_struc_pre@1 EXIT: EBase emp*U@full[xxx_39,y_40]&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [xxx_39;y_40]
 res::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39&{FLOW,(4,5)=__norm#E}[]}<>
 * U@full[y_40]&y_40'=1+y_40& {FLOW,(4,5)=__norm#E}[]
   // add xxx_39'=xxx_39

joiner
======
subst_struc_pre@2
subst_struc_pre inp1 :[(id_38,id_38'),(xxx_39,xxx_39'),(LS,LS'),(LSMU,LSMU'),(waitlevel,waitlevel')]
subst_struc_pre inp2 : EBase 
 id_38::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39&{FLOW,(4,5)=__norm#E}[]}<>*
       U@value[id_38]&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [xxx_39]
                   emp*U@full[xxx_39]&xxx_39'=1+xxx_39&
                   {FLOW,(4,5)=__norm#E}[]

// id_38'::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39[]}<>*U@full[id_38,y_40]@zero[xxx_39]&y_40'=1+0 & xxx_39'=0

subst_struc_pre@2 EXIT: EBase 
  id_38'::Thrd{ + emp*U@full[xxx_39]&xxx_39'=1+xxx_39&{FLOW,(4,5)=__norm#E}[]}<>*
       U@value[id_38]&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [xxx_39]
                   emp*U@full[xxx_39]&xxx_39'=1+xxx_39&
                   {FLOW,(4,5)=__norm#E}[]

  id::Thrd{ + emp*U@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]}<>* U@value[id]&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [x]
                   emp*U@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[]

 State:(exists xxx_1448: (htrue) * 
 id_38'::Thrd{ + emp*N@zero[xxx_39]&{FLOW,(4,5)=__norm#E}[]}<>*U@full[id_38,xxx_39,y_40]
  &xxx_1448=0 & y_40'=1+0 & xxx_1448=1+xxx_39 & xxx_39'=1+xxx_1448&{FLOW,(4,5)=__norm#E}[]

  Why is there a xxx_1448=1+xxx_39??

 */
