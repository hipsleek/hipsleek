data cell {
  int val;
}

int test_fun (cell x, cell y, cell c)
  infer[@shape_prepost]
  requires true
  ensures true;
{
    while (y.val < x.val) 
        infer[@shape_prepost]
        requires true
        ensures true;
      {
            y.val = y.val + 1;
            c.val = c.val + 1;
      }
    return c.val;
}


/*
# norm2/ex5b.ss

# Why are there two c::cell<..> nodes in pre-spec?

 infer[@shape_post GP_3872]requires EXISTS(val_16_3869,val_10_3870,
val_10_3871: c::cell<val_16_3869>@M * x::cell<val_10_3870>@M * 
             c::cell<val_10_3871>@M

!!! INFERRED SHAPE SPEC:
 EInfer @shape_pre[]
   EBase 
     (exists val_16_3869,val_10_3870,
     val_10_3871: c::cell<val_16_3869>@M * x::cell<val_10_3870>@M * 
                  c::cell<val_10_3871>@M&
     {FLOW,(4,5)=__norm#E}[])
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]

[ view HP_2910<y:cell,x:cell>= 
  EBase 
    (exists y_3854,x_3855: self::HP_1587<y_3854,x_3855>@M&
    y_3854=y & x_3855=x&{FLOW,(1,28)=__flow#E}[])equiv_set: ([],HP_1587)
  ,
 view HP_2905<c:cell,y:cell>= 
  EBase 
    self::HP_2950<c>@M&{FLOW,(1,28)=__flow#E}[],
 view HP_2892<x:cell,c:cell>= 
  EBase 
    exists (Impl)[val_10_2902; val_10_2908; 
    val_16_2914](* lbl: *){678}->self::cell<val_10_2902>@M * 
                                 x::cell<val_10_2908>@M * 
                                 c::cell<val_16_2914>@M&
    {FLOW,(1,28)=__flow#E}[]equiv_set: ([],GP_2191)
  ]

*/
