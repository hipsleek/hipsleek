data node {
	int fst;
}

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Down_Separation;
global bool Climb_Inhibit;
global int Up_Separation;
global int Own_Tracked_Alt;
global int Other_Tracked_Alt;
global int Cur_Vertical_Sep;

// error() when index is out of array bound
int int_error() requires true ensures false;

int ALIM()
  requires Positive_RA_Alt_Thresh::node<a> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a> & Alt_Layer_Value = 0 & res = a;
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  return int_error();
}

int Inhibit_Biased_Climb ()
    requires Climb_Inhibit = true ensures Climb_Inhibit = true & res = Up_Separation + 100;
  //  requires Climb_Inhibit = false ensures Climb_Inhibit = false & res = Up_Separation;
{
    if (Climb_Inhibit) return Up_Separation + 100;
    return Up_Separation;
}

bool Own_Above_Threat()
     requires true ensures res = (Other_Tracked_Alt < Own_Tracked_Alt);
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

bool foo()
  requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation) &
  res = ((Down_Separation >= a) & (Cur_Vertical_Sep >= 300));
  //res = ((Down_Separation >= a));

{
  bool r;
  int a;
  bool upward_preferred;

  upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
  if (upward_preferred){
    r  = (Down_Separation > ALIM()) && (Cur_Vertical_Sep >= 300);
  //  r  = (Down_Separation > ALIM());

  } else {
     r = Own_Above_Threat();
  }
  return r;
}

// # true & true & Down_Separation_30<100+Up_Separation_34 & (true | (!(true) &
// !(true))) & Alt_Layer_Value_28=0 & Alt_Layer_Value_28=Alt_Layer_Value_28 &
// Down_Separation_30=Down_Separation_30 & Climb_Inhibit_29=Climb_Inhibit_29 &
// Up_Separation_34=Up_Separation_34 & Own_Tracked_Alt_32=Own_Tracked_Alt_32 &
// Other_Tracked_Alt_31=Other_Tracked_Alt_31 & ((true &
// Other_Tracked_Alt_31<Own_Tracked_Alt_32) | (!(true) &
// !(Other_Tracked_Alt_31<Own_Tracked_Alt_32))) & a_11747=a & Alt_Layer_Value_28=0
// & nv_ALIM=a_11747 & (true | (!(true) & !(true))) &
// nv_Inhibit_Biased_Climb=100+Up_Separation_34 &
// v_int_57_11775+Down_Separation_30=nv_Inhibit_Biased_Climb & 0<v_int_57_11775 &
// v_int_59_11785+nv_ALIM=fff(Down_Separation_30) & 0<v_int_59_11785 |- a_11747=a &
// ((true & a<=Down_Separation_30) | (!(true) & !(a<=Down_Separation_30))) &
// Down_Separation_30<100+Up_Separation_34 & (true | (!(true) & !(true))) &
// Alt_Layer_Value_28=0 
//   # !(true) & true & Down_Separation_30<100+Up_Separation_34 & (true | (!(true)
//   & !(true))) & Alt_Layer_Value_28=0 & Alt_Layer_Value_28=Alt_Layer_Value_28 &
//   Down_Separation_30=Down_Separation_30 & Climb_Inhibit_29=Climb_Inhibit_29 &
//   Up_Separation_34=Up_Separation_34 & Own_Tracked_Alt_32=Own_Tracked_Alt_32 &
//   Other_Tracked_Alt_31=Other_Tracked_Alt_31 & ((true &
//   Other_Tracked_Alt_31<Own_Tracked_Alt_32) | (!(true) &
//   !(Other_Tracked_Alt_31<Own_Tracked_Alt_32))) & a_11747=a &
//   Alt_Layer_Value_28=0 & nv_ALIM=a_11747 & (true | (!(true) & !(true))) &
//   nv_Inhibit_Biased_Climb=100+Up_Separation_34 &
//   v_int_57_11775+Down_Separation_30=nv_Inhibit_Biased_Climb & 0<v_int_57_11775 &
//   v_int_59_11789+nv_ALIM=fff(Down_Separation_30) & v_int_59_11789<=0 |-
//   a_11747=a & ((true & a<=Down_Separation_30) | (!(true) &
//   !(a<=Down_Separation_30))) & Down_Separation_30<100+Up_Separation_34 & (true |
//   (!(true) & !(true))) & Alt_Layer_Value_28=0 

// !!! pure entails:   # 0<v_int_59_11785 &
//     nv_ALIM+v_int_59_11785=fff(Down_Separation_30) & 0<v_int_57_11775 &
//     Other_Tracked_Alt_31<Own_Tracked_Alt_32 &
//     Down_Separation_30<Up_Separation_34+100 &
//     -nv_Inhibit_Biased_Climb+Down_Separation_30+v_int_57_11775=0 &
//     -Up_Separation_34+nv_Inhibit_Biased_Climb-100=0 & a_11747=nv_ALIM &
//     a=a_11747 & Alt_Layer_Value_28=0 |- Down_Separation_30<Up_Separation_34+100
//     & a<=Down_Separation_30 & Alt_Layer_Value_28=0 & a=a_11747 
