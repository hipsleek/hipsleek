relation dom(int[] a, int x, int y) == true.

void initialize(ref int[] Positive_RA_Alt_Thresh)
    requires  dom(Positive_RA_Alt_Thresh, 0, 3)
    ensures  dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
               Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740;
{
    Positive_RA_Alt_Thresh[0] = 400;
    Positive_RA_Alt_Thresh[1] = 500;
    Positive_RA_Alt_Thresh[2] = 640;
    Positive_RA_Alt_Thresh[3] = 740;
}
