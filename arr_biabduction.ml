open Cpure
       
type arrPred =
  | Aseg of (exp * exp * exp)
  | Gap of (exp * exp * exp)
  | Elem of (exp * exp)
;;

let mkAseg b s e =
  Aseg (b,s,e)
;;

let mkGap b s e =
  Gap (b,s,e)
;;

let mkElem b s =
  Elem (b,s)
;;

let isEq s1 e1 pf =
  (* pf |= s1 == e1 *)
  true
;;

let isGt s1 e1 pf =
  (* pf |= s1 > e1 *)
  true
;;

let incOne e =
  e
;;
  
let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let rec helper seqLHS seqRHS antiframe frame =
    match seqLHS, seqRHS with
    | h1::tail1, h2::tail2 ->
       (
         match h1, h2 with
         | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe frame
                  else            (* e1<e2 *)
                    helper tail1 ((mkAseg b1 e1 e2)::tail2) antiframe frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame                  
         | Aseg (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then
                helper ((mkAseg b1 (incOne s1) e1)::tail1) tail2 antiframe frame
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then
                  helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else            (* s1<s2 *)
                  helper seqLHS ((mkGap b1 s1 s2)::seqRHS) antiframe frame
         | Aseg (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then
                if isGt e1 e2 plhs  (* e1>e2 *)
                then helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe ((mkAseg b1 s1 e2)::frame)
                else helper tail1 ((mkGap b2 e1 e2)::tail2) antiframe ((mkAseg b1 s1 e1)::frame)
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame
         | Elem (b1, s1), Elem (b2, s2) ->
            if isEq s1 s2 plhs
            then helper tail1 tail2 antiframe frame
            else
              if isGt s1 s2 plhs
              then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
              else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame
         | Elem (b1, s1), Aseg (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkAseg b2 (incOne s2) e2)::tail2) antiframe frame
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame                            
         | Elem (b1, s1), Gap (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkGap b2 (incOne s2) e2)::tail2) antiframe ((mkElem b1 s1)::frame)
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame (* Just make the gap bigger *)
         | Gap (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkGap b1 e2 e1)::tail1) tail2 antiframe frame
                  else            (* e1<e2 *)
                    helper tail1 ((mkGap b1 e1 e2)::tail2) antiframe frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame                  
         | Gap (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then helper ((mkGap b1 (incOne s1) e1)::tail1) tail2 ((mkElem b2 s2)::antiframe) frame
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame (* Just make the gap bigger *)
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame
         | Gap (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs
                  then helper ((mkGap b1 e2 e1)::tail1) tail2 ((mkAseg b2 s2 e2)::antiframe) frame
                  else helper tail1 ((mkAseg b2 e1 e2)::tail2) ((mkAseg b2 s2 e1)::antiframe) frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame
       )                              
    | h1::tail1, [] ->
       (antiframe,seqLHS@frame)
    | [], h2::tail2 ->
       (seqRHS@antiframe,frame)
    | [],[] ->
       (antiframe, frame)
  in
  helper seqLHS seqRHS [] []
;;
