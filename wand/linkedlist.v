Require Import ZArith.

Module Type Mhip.
 Parameter formula : Type.
 Parameter valid : formula -> Prop.

End Mhip.
