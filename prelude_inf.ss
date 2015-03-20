/*
class __IntegerOverflowErr extends __Error {}

int safe_uadd___(int ui1,int ui2)
// unsigned integer overflow
case{ (\inf - ui1) < ui2 -> ensures true & flow __IntegerOverflowErr;
      (\inf - ui1) >= ui2 -> ensures res = ui1 + ui2;}

int safe_sadd___(int si1, int si2)
// signed integer overflow
case { si1 > 0 -> case { si2 > 0 -> case { si1 > (\inf - si2) -> 
					ensures true & flow __IntegerOverflowErr;
				     si1 <= (\inf - si2) -> ensures res = si1 + si2;
				}
		   si2 <= 0 ->  case{ si2 < (-\inf - si1) ->
					ensures true & flow __IntegerOverflowErr;
				si2 >= (-\inf - si1) -> ensures res = si1 + si2;
				}
		}
 	si1 <= 0 -> case { si2 > 0 -> case { si1 < (-\inf - si2) -> 
				ensures true & flow __IntegerOverflowErr;
				     si1 >= (-\inf - si2) -> ensures res = si1 + si2;
				}
		     si2 <= 0 -> case { si1!=0 & si2 < (\inf - si1) -> 
				ensures true & flow __IntegerOverflowErr;
					si1=0 | si2 >= (\inf - si1) -> 
					ensures res = si1 + si2;}
		}
}
*/
