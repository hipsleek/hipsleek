pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}


void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;

void init1(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i>=0
  ensures base::AsegNE<i,m>;
{

     while(i<m)
        requires base::Aseg<i,m> & i>=0
        ensures base::Aseg<i,m>;
     { 
         upd_arr(base,i,0);
         i = i+1;
     } 
}


// void while_19_5$int~int~arrI(  int i,  int m,  arrI base)
// @ref i
//  rec
// static (stk) EBase 
//    (exists i_1906,m_1907: base::AsegNE<i_1906,m_1907>@M&
//    0<=i & i_1906=i & m_1907=m&{FLOW,(4,5)=__norm#E}[])
//    EBase 
//      emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
//      EAssume 
//        ref [i]
//        (exists i_1908,flted_21_1905: base::AsegNE<i_1908,flted_21_1905>@M&
//        flted_21_1905=1+m & i_1908=i&{FLOW,(4,5)=__norm#E}[])
//        struct:EBase 
//                 (exists i_1909,
//                 flted_21_1904: base::AsegNE<i_1909,flted_21_1904>@M&
//                 flted_21_1904=1+m & i_1909=i&{FLOW,(4,5)=__norm#E}[])
// dynamic  EBase 
//    hfalse&false&{FLOW,(4,5)=__norm#E}[]
// {(boolean v_bool_19_1961;
//    (v_bool_19_1961 = {lt___$int~int(i,m)};
//     if (v_bool_19_1961)
//      [{({i = {((int v_int_24_1954;
//      v_int_24_1954 = 1);
//      add___$int~int(i,v_int_24_1954))}}
//      ;
//      {while_19_5$int~int~arrI(i,m,base) rec})}]
//    else
//      []
// ))}
