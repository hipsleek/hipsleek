  
void main()
  requires true ensures true;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  { int kk =1;
    v = v +kk;
    dprint;
  }
  dprint;
}

/*
# ex14.ss

Successful States:
[
 Label: []
 State:htrue*@full[x_36,y_37,v_38,kk_39]&v_38'=kk_39'+v_1343 & v_1343=5 & y_37'=40 & x_36'=4 & kk_39'=1&{FLOW,(4,5)=__norm#E}[]

 ]

void main()
  requires true ensures true;
{
  int x,y,v;
  x=4; y=40; v=5;
  dprint;
  { int kk =1;
    v = v +kk;
    dprint;
  }
  kk = x;
  dprint;
}

# need to remove kk_39 from the varperm list at the end of k-scope

dprint: ex14-varperm-block.ss:12: ctx:  List of Failesc Context: [FEC(0, 0, 1  [])]

Successful States:
[
 Label: []
 State:htrue*@full[x_36,y_37,v_38,kk_39]&v_38'=1+v_1343 & v_1343=5 & y_37'=40 & x_36'=4&{FLOW,(4,5)=__norm#E}[]

 ]
*/
