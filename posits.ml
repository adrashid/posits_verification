(* ========================================================================= *)
(*                                                                           *)
(*                     Formal Verification of Unum                           *)
(*                                                                           *)
(*    (c) Copyright, Adnan Rashid*, Ayesha Gauhar*, Osman Hasan*             *)
(*                   Sa'ed Abed** & Imtiaz Ahmed**                           *)
(*       *System Analysis and Verification (SAVe) Lab,                       *)
(*        National University of Sciences and Technology (NUST), Pakistan    *)
(*                                                                           *)
(*       **Computer Engineering Department,                                  *)
(*         College of Engineering and Petroleum, Kuwait University, Kuwait   *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Library/calc_real.ml";;
needs "Multivariate/misc.ml";;



unparse_as_infix("ipow");;
let ipow = define
  `ipow (x:real) (e:int) = 
  (if (&0 <= e)
   then (x pow (num_of_int e))
   else (inv (x pow (num_of_int (--e)))))`;;
parse_as_infix("ipow",(24,"left"));;

let BV   = new_definition `BV b =if b then 1 else 0`;;

let num2bool = new_definition `num2bool (n:num) = if (n = 0) then F else T`;;


let num_BV = define`(num_BV 0 a = [] ) /\
(num_BV (SUC n) a = (CONS (num2bool (a MOD 2))  (num_BV (n) (a DIV 2))))`;;

let num_BV_f = new_definition `num_BV_f n a = REVERSE (num_BV n a)`;;


let BV_n  = define `(BV_n [] = 0) /\  (BV_n (CONS h t) = 
(2 EXP (LENGTH t)) * BV h + BV_n t) `;;

let not_0 = define
` (not_0 []  = []) /\
(not_0 (CONS h t)  = (CONS (~h)  (not_0 t)))`;;

let not_n = define
`not_n (CONS h t) out = (out = not_0 (CONS h t))`;;

(*__________________________________Definitions ________________________________*)

let two_complement = new_definition
`two_complement L = num_BV_f (LENGTH L)(BV_n (not_0 (L)) + 1)`;;

let is_valid_posit = new_definition`!(nb:int)(es:int). is_valid_posit (nb, es) = 
((nb>=(int_of_num(2))) /\ (es>=(int_of_num(0)))) `;;

g`?(pst:int#int). is_valid_posit pst`;;
 e(EXISTS_TAC`&2:int,&2:int`);;
 e(REWRITE_TAC[is_valid_posit]);;
e(ARITH_TAC);;
let PROOF_TYPE = top_thm();;
let posforamt_tpbij = new_type_definition"posit" ("mk_posit", "dest_posit") 
(prove(`?(pst:int#int). is_valid_posit pst`, REWRITE_TAC[PROOF_TYPE]));;

let num_of_real = new_definition`!(a:real).num_of_real a = num_of_int(int_of_real (a))`;;
let ebits_num =  new_definition` ebits_num P =num_of_int(SND (dest_posit P))`;;

let nbits_num =  new_definition` nbits_num P =num_of_int(FST (dest_posit P))`;;

let useed = new_definition`!(p:posit). useed p = &2 pow (2 EXP (ebits_num p))`;;
(*no_of pattrens*)
let npat = new_definition`!(p:posit) . npat p = &2 pow (nbits_num p)`;;

let maxpos = new_definition `!(p:posit). maxpos p = (useed (p)) pow ((nbits_num p) - 2)`;;

let minpos = new_definition `!(p:posit). minpos p = &1/ (maxpos p)`;;

let  is_valid_posit_length = new_definition`is_valid_posit_length (P:posit) (L:bool list) = (LENGTH L = nbits_num P)`;;

let zero_exception = new_definition`zero_exception L = ~(MEM (T) L)`;;
let inf_exception = new_definition `inf_exception L =  ((HD L) /\ ~(MEM T L)) `;; 

(*----Check maximum positve pattren (maxpos)---------*)
let checkmax = new_definition ` checkmax L =  ~(MEM F (TL L))`;;

let sign_bit = new_definition`!(L: (bool) list). sign_bit L =  HD L `;; 

let value_of_k = new_recursive_definition list_RECURSION
`(value_of_k [] = (&0:int)) /\
(value_of_k (CONS (h:bool) t)  = 
if (HD t) 
then (if (((HD t)= HD (TL (t))) /\ (~((LENGTH t) <= 1 )) )
      then ((value_of_k t) + (&1:int)) 
      else (&0:int)) 
else (if (((HD t)= HD (TL (t))) /\ (~((LENGTH t) <= 1 )))
     then  ((value_of_k t) - (&1:int)) 
     else ((--(&1)):int)))`;;

let scale_factor_r = new_definition`scale_factor_r P L =
(useed P) ipow (value_of_k L) `;;


let regime_length = new_definition`regime_length L = 
if (abs(value_of_k L) < (&(LENGTH L)- &2))/\ (LENGTH L >2)
then  (if (~(HD (TL L))) 
      then ((num_of_int(abs(value_of_k L))) +1)
      else  ((num_of_int(value_of_k L))+2) )
 else ((LENGTH L)-1) `;;
 
let pick_elements_simp = define`
pick_elements_simp L l 0 = [] /\
pick_elements_simp L l (SUC n) = CONS (EL l L) (pick_elements_simp L (l+1) n) `;;

let pick_elements = new_definition`pick_elements (L) (l:num) (u:num) =
         pick_elements_simp (L) (l) ((u -l) + 1)`;;

let exp_bits = new_definition`!(P:posit) L. exp_bits P L = 
if ((regime_length L) +1) < (nbits_num P) /\ (1<= (ebits_num P))
 then (if ( ((regime_length L) +1 + (ebits_num P))
 <= LENGTH (L))  then
pick_elements L ((regime_length L) +1)  
( (regime_length L) + (ebits_num P)) 
else pick_elements L ( (regime_length L) +1 ) (LENGTH L-1) )  else []`;;

let exp_length = new_definition`exp_length P L = LENGTH (exp_bits P L)`;;

let scale_factor_e = new_definition`scale_factor_e P L = 
((&2) pow ((BV_n (exp_bits P L))*(2 EXP ((ebits_num P) - (exp_length P L))))) `;; 


let fraction_bits = new_definition`!(P:posit) L . fraction_bits P L = 
if ((regime_length L) + (exp_length P L) +1 < (nbits_num P) ) then 
pick_elements L ((regime_length L) + (exp_length P L) +1) ((nbits_num P) - 1 ) else []`;;

let fraction_length = new_definition`fraction_length P L = LENGTH (fraction_bits P L)`;;

let scale_factor_f = new_definition`scale_factor_f P L =  &1 +(&(BV_n (fraction_bits P L)) / ((&2) pow (fraction_length P L )))`;;

let posit_to_signed_real1 = new_definition`posit_to_signed_real1 P L = 
if (checkmax L) then (if (sign_bit L) then -- ((&1)/ maxpos P) else (maxpos P))
 else (if (sign_bit L) 
then -- ((scale_factor_r P (two_complement L))*
(scale_factor_e P (two_complement L))*(scale_factor_f P (two_complement L)))
else ((scale_factor_r P L)*(scale_factor_e P L)*(scale_factor_f P L)))`;;


let posit_to_signed_real = new_definition`posit_to_signed_real P L = 
if (checkmax L) then (if (sign_bit L) then -- ((&1)/ maxpos P) else (maxpos P))
 else (if (sign_bit L) 
then -- ((scale_factor_r P (CONS (sign_bit L) (two_complement (TL L))))*
(scale_factor_e P (CONS (sign_bit L) (two_complement (TL L))))*(scale_factor_f P (CONS (sign_bit L) (two_complement (TL L)))))
else ((scale_factor_r P L)*(scale_factor_e P L)*(scale_factor_f P L)))`;;



let add_zero_real = new_definition`add_zero_real P L = if zero_exception L then (&0) else 
posit_to_signed_real P L`;;

(*--------Encoding from real to posit----------------*)

let sign_real = new_definition`sign_real x = (x<(&0))`;;


let get_regime_ones = define`(get_regime_ones (x:real) (p:posit) 0 = [T] ) /\
(get_regime_ones x p (SUC n) = if ((&1) <= x) /\ (x < (useed p)) 
then CONS T (CONS F NIL) else
CONS T (get_regime_ones (x /(useed p)) p n))`;;


let get_regime_zeros = define`(get_regime_zeros (x:real) (p:posit) 0 =if (x=(&0)) then [F] else [T]) /\
(get_regime_zeros x p (SUC n) = if (&1<=x) 
then (CONS T NIL) else
CONS F (get_regime_zeros (x * (useed p)) p n))`;;

let regime_bits = new_definition`regime_bits   x P = if ( &1<=x) 
then (get_regime_ones x P ((nbits_num P) -2)) 
else (get_regime_zeros x P ((nbits_num P) -2))`;;

let exp_bits_value = define`(exp_bits_value (x:real) 0 = 0) /\
(exp_bits_value x (SUC n) = if(((&1)<=x) /\ (x< (&2))) then (0)
else ((exp_bits_value (x/(&2)) n) + 1))`;;

let exp_list = new_definition`exp_list  x P = num_BV_f (ebits_num P)
(exp_bits_value (x /(scale_factor_r P (APPEND [(sign_real x)] (regime_bits x P)))) 
((2 EXP (ebits_num P)) - 1 ))`;;

let exponential_round_check1 = new_definition`exponential_round_check1 x P =
 ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1)) < (ebits_num P)`;;

let te_bits = new_definition`te_bits x P = 
(ebits_num P) - ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1))`;;

let exp_up = new_definition`exp_up x P = 
(((BV_n (exp_list x P)) DIV (2 EXP (te_bits x P))) + 1) * (2 EXP (te_bits x P))`;;


let exp_down = new_definition`exp_down x P = 
((BV_n (exp_list x P)) DIV (2 EXP (te_bits x P))) * (2 EXP (te_bits x P))`;;

let exp_posit_up = new_definition`exp_posit_up x P = 
if (exp_up x P) < (2 EXP ebits_num P) then
APPEND (regime_bits x P) (num_BV_f ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1))
(exp_up x P))
else 
if HD (regime_bits x P) then APPEND (CONS T (regime_bits x P)) 
(num_BV_f ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1) - 1) (0))
else APPEND (TL  (regime_bits x P)) 
(num_BV_f ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1)+ 1) (0))`;;

let exp_posit_down = new_definition`exp_posit_down x P = 
APPEND (regime_bits x P) (num_BV_f ((nbits_num P) - ((LENGTH (regime_bits x P)) + 1))
(exp_down x P))`;;



let te_rounded_bits = new_definition`te_rounded_bits x P =  
BV_n (pick_elements (exp_list x P) 
((nbits_num P) - ((LENGTH (regime_bits x P)) + 1))((ebits_num P) - 1))`;;


let exp_posit_tie = new_definition`exp_posit_tie x P = if LAST (exp_posit_down x P) then 
(exp_posit_up x P) else (exp_posit_down x P)`;;

let exp_residue = new_definition` exp_residue x P = 
~(((x/((scale_factor_r P (APPEND [(sign_real x)] (regime_bits x P)))* (&2 pow BV_n (exp_list x P)))) - (&1)) = (&0))`;;

let exponential_rounding1 = new_definition`exponential_rounding1 x P =
 if ~(exp_residue x P) /\ ((te_rounded_bits x P) = 
(2 EXP ((te_bits x P) - 1 )))
 then (exp_posit_tie x P) 
else 
( if ((exp_residue x P) /\ ((te_rounded_bits x P) = 
(2 EXP ((te_bits x P)- 1 )))) 
\/ ((te_rounded_bits x P) >
(2 EXP ((te_bits x P) - 1 )))
then (exp_posit_up x P )
 else (exp_posit_down x P ))`;;

let fraction_list = define`(fraction_list (x:real) 0 =[])/\
(fraction_list x (SUC n) = if (&1<=x*(&2)) then 
(CONS T (fraction_list ((&2*x)-(&1)) n)) 
else (CONS F (fraction_list (x*(&2)) n)))`;;


let set_fraction_list = new_definition`set_fraction_list x P = 
fraction_list 
((x/((scale_factor_r P (APPEND [(sign_real x)] (regime_bits x P)))* (&2 pow BV_n (exp_list x P))))-(&1)) 
((nbits_num P) - (LENGTH (regime_bits x P))- (ebits_num P)-1)`;;


let fraction_residue1 = define`(fraction_residue1 (x:real) 0 = x)/\
(fraction_residue1 x (SUC n) = if (&1<=x*(&2)) then 
(fraction_residue1 ((&2*x)-(&1)) n) 
else (fraction_residue1 (x*(&2)) n))`;; 

let fraction_residue_set1 = new_definition`fraction_residue_set1 x P = 
fraction_residue1 ((x/((scale_factor_r P (APPEND [(sign_real x)] (regime_bits x P)))* 
(&2 pow BV_n (exp_list x P))))-(&1)) 
((nbits_num P) - (LENGTH (regime_bits x P))- (ebits_num P)-1)`;;

 
let frac_posit_up = new_definition`frac_posit_up x P =
num_BV_f ((nbits_num P)-1)
(BV_n (APPEND (regime_bits x P) (APPEND (exp_list x P)(set_fraction_list x P))) + 1)
`;;


let frac_posit_down = new_definition`frac_posit_down x P =
 (APPEND (regime_bits x P) (APPEND (exp_list x P)(set_fraction_list x P)))`;;

let frac_posit_tie = new_definition`frac_posit_tie x P = if LAST (frac_posit_down x P) then 
(frac_posit_up x P) else (frac_posit_down x P)`;;

let fraction_rounding1 = new_definition`fraction_rounding1 x P = 
if (fraction_residue_set1 x P = (&0))
then (APPEND (regime_bits x P) (APPEND (exp_list x P)(set_fraction_list x P)))
 else (if ((fraction_residue_set1 x P ) = ((&1)/(&2))) then (frac_posit_tie x P) 
else (if ((fraction_residue_set1 x P ) > ((&1)/(&2))) then  (frac_posit_up x P)
 else  (frac_posit_down x P)))`;;

let maxpos_posit = new_definition`maxpos_posit P = 
num_BV_f ((nbits_num P) - 1 )( (2 EXP ((nbits_num P) - 1)) - 1)`;;

let minpos_posit = new_definition`minpos_posit P = 
num_BV_f ((nbits_num P) - 1 )( 1)`;;

let sign_real = new_definition`sign_real x = (x<(&0))`;;



let real_to_posit_check3 = new_definition`real_to_posit_check3 x P=
 if ((x = (&0))\/((abs x) >=(maxpos P) )\/(((abs x) <= minpos P))) 
then (if (x = (&0)) 
     then (APPEND [F]  (regime_bits x P)) 
     else (if ((abs x) >=(maxpos P) ) 
     	  then CONS (sign_real x) 
	  (if (sign_real x) then two_complement (maxpos_posit P) else (maxpos_posit P)) 
	  else CONS (sign_real x) 
	  (if (sign_real x) then two_complement (minpos_posit P) else (minpos_posit P) )))
else(if x>(&0)  
       then (if (exponential_round_check1 x P) 
      	       then APPEND [F] (exponential_rounding1 x P)
      	       else APPEND [F] (fraction_rounding1 x P))
       else (if (exponential_round_check1 (abs x) P) 
      	       then APPEND [T] (two_complement (exponential_rounding1 (abs x) P))
      	       else APPEND [T] (two_complement (fraction_rounding1 (abs x) P))))`;;
			   


(*__________________________________Properties________________________________*)


let RECIPROCAL_LE = prove
 (`!n.((&1)<=n)==>((&1)/n <=n)`,
  GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(&0)<n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC [REAL_LE_LDIV_EQ; real_gt] THEN
  SIMP_TAC [REAL_LE_SQUARE; GSYM REAL_POW_2] THEN STRIP_TAC THEN
  ASM_SIMP_TAC [REAL_POW_LE_1]);;


let NEG_RECIPROCAL_LE = prove
 (`!n.((&1)<=n)==>( --((&1)/n)<=n)`,
  GEN_TAC THEN STRIP_TAC THEN SIMP_TAC [REAL_LE_LNEG] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN STRIP_TAC THENL
   [SIMP_TAC [] THEN SIMP_TAC [REAL_LE_LT] THEN DISJ1_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC [REAL_LT_01];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

let NEG_POW_LE = prove
 (`!n m. --((&2) pow n)<=(&2) pow m`,
  REPEAT GEN_TAC THEN SIMP_TAC [REAL_LE_LNEG] THEN SIMP_TAC [REAL_LE_LT] THEN
  DISJ1_TAC THEN SIMP_TAC [REAL_LT_POW2; REAL_LT_ADD]);;


let MAXPOS_GE_1 = prove
 (`! P. &1<=maxpos P`,
  SIMP_TAC [maxpos; useed] THEN SIMP_TAC [REAL_LE_POW2; REAL_POW_LE_1]);;


let MAXPOS_GT_0 = prove
 (`! P. &0< maxpos P`,
  SIMP_TAC [maxpos; useed] THEN ASM_SIMP_TAC [REAL_LT_POW2; REAL_POW_POW]);;


let POSITFORMAT_SPLIT = TAUT `!(pst:posit).
  (dest_posit pst) = (FST (dest_posit pst),
                         SND (dest_posit pst))`;;


let POSIT_VALID_LENGTH_GE_2 =
  prove(`!(n:int) (e:int). ((is_valid_posit (n,e)) ==>
(&2) <= (FST (n,e)))`,REPEAT GEN_TAC THEN REWRITE_TAC[is_valid_posit] THEN ARITH_TAC);;


let K_GE_0 = prove
 (`!L.(HD (TL (L)))==> value_of_k (L) >= (&0)`,
  LIST_INDUCT_TAC THEN SIMP_TAC [HD; TL; value_of_k] THENL
   [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN ONCE_SIMP_TAC [INT_GE] THEN
  STRIP_TAC THEN MATCH_MP_TAC INT_LE_ADD THEN SIMP_TAC [INT_LE_01] THEN
  SIMP_TAC [GSYM INT_GE] THEN
  UNDISCH_TAC `HD (TL (t:(bool)list)) /\ ~(LENGTH (t:(bool)list) <= 1)` THEN
  STRIP_TAC THEN ASM_SIMP_TAC []);;


let NOT_VALID_LENGTH_1 = prove
 (`(is_valid_posit_length P (CONS h t)) ==> ~( is_valid_posit_length P t)`,
  SIMP_TAC [is_valid_posit_length; LENGTH] THEN SIMP_TAC [ADD1] THEN
  ARITH_TAC);;

let NOT_VALID_LENGTH_2 = prove
 (`( is_valid_posit_length P t) ==>  ~(is_valid_posit_length P (CONS h t))`,
  SIMP_TAC [is_valid_posit_length; LENGTH] THEN SIMP_TAC [ADD1] THEN
  ARITH_TAC);;

let ZERO_EXCEPTION = prove
 (`~zero_exception t ==> ~zero_exception (CONS h t)`,
  SIMP_TAC [zero_exception; MEM]);;


let INF_EXCEPTION = prove
 (`(~(zero_exception t))/\(~inf_exception t) ==> ~inf_exception (CONS h t)`,
  SIMP_TAC [inf_exception; MEM; zero_exception]);;


let EXIST_LESS_k = prove
 (`!n. ?L .(HD (TL L)) /\ (&(LENGTH L) = n) /\ (n>=(&2)) 
==> (value_of_k L) <= &(LENGTH L) - (&2)`,
  GEN_TAC THEN EXISTS_TAC `[T;T;F]` THEN SIMP_TAC [value_of_k] THEN
  ONCE_SIMP_TAC [HD; TL] THEN ONCE_SIMP_TAC [HD; TL] THEN
  ONCE_SIMP_TAC [HD; TL] THEN ONCE_SIMP_TAC [HD; TL] THEN SIMP_TAC [LENGTH] THEN
  ARITH_TAC);;


let IS_VALID_POSIT = prove
 (`!P. is_valid_posit (dest_posit P)`,
  SIMP_TAC [PROOF_TYPE; posforamt_tpbij]);;

let FST_POSIT_NUM = prove
 (`!P. (is_valid_posit (dest_posit P)) ==>  
&(num_of_int (FST (dest_posit P))) = FST (dest_posit P)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0<=FST (dest_posit P)` ASSUME_TAC THENL
   [ALL_TAC; POP_ASSUM MP_TAC THEN SIMP_TAC [INT_OF_NUM_OF_INT]] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `(&2:int)` THEN STRIP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `is_valid_posit (dest_posit P)` THEN
  ONCE_REWRITE_TAC [POSITFORMAT_SPLIT; POSIT_VALID_LENGTH_GE_2] THEN
  ONCE_REWRITE_TAC [POSITFORMAT_SPLIT; POSIT_VALID_LENGTH_GE_2]);;


let FST_NUM_INT = prove
 (`!P. &(nbits_num P) = FST (dest_posit P)`,
  ONCE_REWRITE_TAC [POSITFORMAT_SPLIT; nbits_num] THEN SIMP_TAC [] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC FST_POSIT_NUM THEN
  SIMP_TAC [IS_VALID_POSIT]);;


let NBITS_GE_2 = prove
 (`!P. 2<= nbits_num P`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM INT_OF_NUM_LE] THEN
  ONCE_SIMP_TAC [FST_NUM_INT] THEN ONCE_REWRITE_TAC [POSITFORMAT_SPLIT] THEN
  MATCH_MP_TAC POSIT_VALID_LENGTH_GE_2 THEN SIMP_TAC [IS_VALID_POSIT]);;


let POSIT_VALID_LENGTH_EXP_GE_0 =
  prove(`!(n:int) (e:int). ((is_valid_posit (n,e)) ==>
(&0) <= (SND (n,e)))`,REPEAT GEN_TAC THEN REWRITE_TAC[is_valid_posit] THEN ARITH_TAC);;

let SND_POSIT_NUM = prove
 (`!P. (is_valid_posit (dest_posit P)) ==>  
&(num_of_int (SND (dest_posit P))) = SND (dest_posit P)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [POSITFORMAT_SPLIT; POSIT_VALID_LENGTH_EXP_GE_0] THEN
  ONCE_REWRITE_TAC [POSITFORMAT_SPLIT; POSIT_VALID_LENGTH_EXP_GE_0]);;


let SND_NUM_INT = prove
 (`!P. &(ebits_num P) = SND (dest_posit P)`,
  REWRITE_TAC [ebits_num] THEN GEN_TAC THEN MATCH_MP_TAC SND_POSIT_NUM THEN
  SIMP_TAC [IS_VALID_POSIT]);;

let EXP_GE_0 = prove
 (`!P.0<= ebits_num P`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM INT_OF_NUM_LE] THEN
  SIMP_TAC [ebits_num; SND_NUM_INT] THEN ONCE_REWRITE_TAC [POSITFORMAT_SPLIT] THEN
  MATCH_MP_TAC POSIT_VALID_LENGTH_EXP_GE_0 THEN SIMP_TAC [IS_VALID_POSIT]);;


let LENGTH_PICK_ELEM1 = prove
 (`!n L m  .LENGTH (pick_elements_simp L m n ) = n`,
  INDUCT_TAC THENL
   [SIMP_TAC [pick_elements_simp; LENGTH];
    ASM_SIMP_TAC [pick_elements_simp; LENGTH]]);;


let LENGTH_PICK_ELEM = prove
 (`!L l u  .LENGTH (pick_elements L l (u)) = (u-l)+1`,
  SIMP_TAC [pick_elements; LENGTH_PICK_ELEM1]);;


let L_ADD1 = prove
 (`!n m  L. pick_elements_simp (L) (SUC m) (n) = (pick_elements_simp (TL L) m (n))`,
  INDUCT_TAC THENL
   [SIMP_TAC [pick_elements_simp];
    ASM_SIMP_TAC [pick_elements_simp; TL; GSYM ADD1; EL]]);;


let PICK_FULL_LIST = prove
 (`! (L:bool list). pick_elements_simp L 0 (LENGTH L)= L`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [HD; SUB_0; ONE; ADD_CLAUSES; pick_elements_simp; LENGTH];
    SIMP_TAC [EL; HD; pick_elements_simp; LENGTH] THEN
    ASM_REWRITE_TAC [L_ADD1; GSYM ADD1; TL]]);;


let FULL_LIST_BOUND = prove
 (`! (L:bool list).(~(L=[]))==>( pick_elements L 0 (LENGTH L-1)= L)`,
  SIMP_TAC [pick_elements; GSYM LENGTH_EQ_NIL; GSYM LT_NZ] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(LENGTH (L:(bool)list) - 1 - 0 + 1)=  LENGTH (L:(bool)list)`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC [PICK_FULL_LIST]]);;


let HD_PICK_ELEM = prove
 (`!n L m . HD (pick_elements L m n ) = EL m L`,
  INDUCT_TAC THEN
  SIMP_TAC [pick_elements; HD; SUB_0; ONE; ADD_CLAUSES; pick_elements_simp]);;


let SND_LIST_APPEND = prove
 (`! (A:bool list) (B:bool list) .(0<LENGTH B)==>
pick_elements_simp (APPEND A B)(LENGTH A) (LENGTH B) = B`,
  LIST_INDUCT_TAC THENL [SIMP_TAC [APPEND; LENGTH; PICK_FULL_LIST]; ALL_TAC] THEN
  SIMP_TAC [LENGTH; LT_REFL] THEN SIMP_TAC [LENGTH; pick_elements_simp] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EL; HD; APPEND; GSYM ADD1; L_ADD1; TL]);;


let PICK_LIST_APPEND4 = prove
 (`! (A:bool list) (B:bool list) (C:bool list). (0<LENGTH B)/\(0<LENGTH C)==>
pick_elements (APPEND A (APPEND B C)) ((LENGTH(A))+(LENGTH B))((LENGTH(A))+(LENGTH B)+ (LENGTH C) -1)= C`,
  SIMP_TAC [pick_elements] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `((LENGTH (A:(bool)list) + LENGTH (B:(bool)list) + LENGTH (C:(bool)list) - 1) - (LENGTH (A:(bool)list)+ LENGTH (B:(bool)list)) +
  1) = LENGTH C`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [SND_LIST_APPEND; APPEND_ASSOC; GSYM LENGTH_APPEND]);;


let FRTH_LIST_APPEND = prove
 (`! (A:bool list) (B:bool list) . (0<LENGTH C)==>
pick_elements_simp (APPEND A (APPEND B C)) ((LENGTH(A))+(LENGTH B)) (LENGTH C) = C`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; APPEND; SND_LIST_APPEND; ADD_CLAUSES]; ALL_TAC] THEN
  SIMP_TAC [LENGTH; pick_elements_simp] THEN REPEAT STRIP_TAC THEN
  ONCE_SIMP_TAC
    [ARITH_RULE
       `SUC (LENGTH (t:(bool)list)) + LENGTH (B:(bool)list) =
SUC (LENGTH (t:(bool)list) + LENGTH (B:(bool)list))`] THEN
  ASM_SIMP_TAC [EL; HD; APPEND; GSYM ADD1; L_ADD1; TL]);;


let PICK_LIST_APPEND2 = prove
 (`! (A:bool list) (B:bool list) . (0< LENGTH A)/\(0<LENGTH B)==>
pick_elements (APPEND A B) (LENGTH A)((LENGTH(A))+(LENGTH B ) -1)= B`,
  SIMP_TAC [pick_elements] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `((LENGTH (A:(bool)list) + LENGTH (B:(bool)list) - 1) - LENGTH (A:(bool)list) +
  1) = LENGTH B`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC [SND_LIST_APPEND]]);;


let PST_EXP_LENGTH = prove
 (`!P (L:bool list).(is_valid_posit_length P L)==> (exp_length P L) <= ebits_num P`,
  SIMP_TAC [exp_bits; exp_length] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [COND_CASES_TAC THEN SIMP_TAC [LENGTH_PICK_ELEM] THEN ASM_ARITH_TAC;
    SIMP_TAC [LENGTH; EXP_GE_0]]);;


let VAL_LT_EXP2 = prove
 (`!a. BV_n a < 2 EXP LENGTH a`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; BV_n] THEN SIMP_TAC [LENGTH; BV_n; ADD1] THEN
    SIMP_TAC [EXP_ADD] THEN SIMP_TAC [GSYM REAL_OF_NUM_LT] THEN
    SIMP_TAC [GSYM REAL_OF_NUM_POW] THEN SIMP_TAC [REAL_LT_POW2];
    SIMP_TAC [BV_n; BV; LENGTH] THEN COND_CASES_TAC THENL
     [SIMP_TAC [EXP; MULT_CLAUSES] THEN SIMP_TAC [MULT_2] THEN
      SIMP_TAC [LT_ADD_LCANCEL] THEN ASM_SIMP_TAC [];
      SIMP_TAC [ADD_0; MULT_0; ADD_SYM] THEN SIMP_TAC [EXP] THEN
      ASM_ARITH_TAC]]);;


let CHECKMAX = prove
 (`(HD t)==>((~checkmax (CONS h t)) ==>  ~(checkmax t))`,
  SIMP_TAC [checkmax; HD; MEM; TL] THEN ASM_CASES_TAC `(t:bool list)=[]` THENL
   [ASM_SIMP_TAC [IMP_CLAUSES; MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:bool list) = CONS (HD t)(TL t)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONS_HD_TL THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [MEM] THEN
  SIMP_TAC [HD; OR_CLAUSES; IMP_CLAUSES] THEN SIMP_TAC [TL]);;


let SCALE_EXP_LE = prove
 (`!P L. (is_valid_posit_length P L)==> scale_factor_e P L <= &(2 EXP (2 EXP ebits_num P))`,
  SIMP_TAC [GSYM REAL_OF_NUM_POW] THEN SIMP_TAC [scale_factor_e] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_MONO THEN STRIP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `&2 pow
 (ebits_num (P:posit) - (exp_length (P:posit) (L:(bool)list))) = &2 pow
 (ebits_num (P:posit))/(&2) pow ( (exp_length (P:posit) (L:(bool)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_SUB THEN STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PST_EXP_LENGTH THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC
    [GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN
    `(&(BV_n (exp_bits (P:posit) (L:(bool)list)))) 
* ((&2) pow ebits_num (P:posit)) /
 ((&2) pow  (exp_length (P:posit) (L:(bool)list))) =
 ((&(BV_n (exp_bits (P:posit) (L:(bool)list)))) * ((&2) pow ebits_num (P:posit))) /
 ((&2) pow (exp_length (P:posit) (L:(bool)list)))`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
  ONCE_REWRITE_TAC
    [ARITH_RULE
       `(&(BV_n (exp_bits (P:posit) (L:(bool)list)))) * &2 pow ebits_num (P:posit) = 
 &2 pow ebits_num (P:posit) *(&(BV_n (exp_bits (P:posit) (L:(bool)list))))`] THEN
  ASM_SIMP_TAC [REAL_LE_LMUL_EQ; REAL_LT_POW2] THEN SIMP_TAC [REAL_LE_LT] THEN
  DISJ1_TAC THEN SIMP_TAC [REAL_OF_NUM_LT; REAL_OF_NUM_POW] THEN
  SIMP_TAC [VAL_LT_EXP2; exp_length]);;


let VAL_LE_EXP2 = prove
 (`!a. BV_n a <= (2 EXP LENGTH a)-1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `2 EXP  LENGTH (a:(bool)list) - 1 + 1 = 2 EXP LENGTH (a:(bool)list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_ADD THEN
    SIMP_TAC [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_LE_POW2];
    ASM_SIMP_TAC [GSYM LT_SUC_LE; ADD1; VAL_LT_EXP2]]);;

	

let EXP_LENGTH_NT_ES = prove
 (`!L P. (is_valid_posit_length P L)/\ (nbits_num P - (regime_length L +1) < ebits_num P
)==> (exp_length P L) <= (nbits_num P) - ((regime_length L)+1)`,
  REPEAT STRIP_TAC THEN SIMP_TAC [exp_length; exp_bits] THEN COND_CASES_TAC THENL
   [UNDISCH_TAC `is_valid_posit_length (P:posit) (L:(bool)list)` THEN
    SIMP_TAC [is_valid_posit_length] THEN STRIP_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC [LENGTH_PICK_ELEM];
    ASM_SIMP_TAC [LENGTH] THEN ASM_SIMP_TAC [nbits_num]] THEN
  ASM_ARITH_TAC);;


let EXP_LENGTH_NT_GE = prove
 (`~(exp_length (P:posit) (L:(bool)list) < ebits_num (P:posit)) ==> exp_length P L = ebits_num P`,
  SIMP_TAC [NOT_LT; LE_LT] THEN SIMP_TAC [exp_length; exp_bits] THEN
  REPEAT COND_CASES_TAC THEN SIMP_TAC [LENGTH_PICK_ELEM; LENGTH] THENL
   [STRIP_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;


let SCALE_EXP_LE_1 = prove
 (`!P L. (is_valid_posit_length P L)==> scale_factor_e P L <= 
&(2 EXP ((2 EXP ebits_num P)-1))`,
  SIMP_TAC [GSYM REAL_OF_NUM_POW] THEN SIMP_TAC [scale_factor_e] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_MONO THEN STRIP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC [GSYM LT_SUC_LE] THEN SIMP_TAC [ADD1] THEN
  SUBGOAL_THEN
    `2 EXP ebits_num (P:posit) - 1 + 1 = 2 EXP ebits_num (P:posit)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_ADD THEN
    SIMP_TAC [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_LE_POW2];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `&2 pow
 (ebits_num (P:posit) - (exp_length (P:posit) (L:(bool)list))) = &2 pow
 (ebits_num (P:posit))/(&2) pow ( (exp_length (P:posit) (L:(bool)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_SUB THEN STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PST_EXP_LENGTH THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  ASM_SIMP_TAC
    [GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `(&0)< &2 pow (exp_length (P:posit) (L:(bool)list))`
    ASSUME_TAC THENL
   [SIMP_TAC [REAL_LT_POW2]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(&(BV_n (exp_bits (P:posit) (L:(bool)list)))) 
* ((&2) pow ebits_num (P:posit)) /
 ((&2) pow  (exp_length (P:posit) (L:(bool)list))) =
 ((&(BV_n (exp_bits (P:posit) (L:(bool)list)))) * ((&2) pow ebits_num (P:posit))) /
 ((&2) pow (exp_length (P:posit) (L:(bool)list)))`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN
  SIMP_TAC
    [ARITH_RULE
       `((&2) pow (ebits_num (P:posit))) * 
((&2) pow ( exp_length (P:posit) (L:(bool)list) )) 
= ((&2) pow (exp_length (P:posit) (L:(bool)list)))*((&2) pow (ebits_num (P:posit)))`] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN
  SIMP_TAC
    [VAL_LT_EXP2; exp_length; REAL_LT_POW2; REAL_OF_NUM_LT; REAL_OF_NUM_POW]);;


let SCALE_EXP_GT_0 = prove
 (`!L P.(is_valid_posit_length P L)==>(&0)<(scale_factor_e P L)`,
  REPEAT GEN_TAC THEN SIMP_TAC [scale_factor_e] THEN SIMP_TAC [REAL_LT_POW2]);;


let FRAC_LE_1 = prove
 (`!P L. (is_valid_posit_length P L)==> (scale_factor_f P L)-(&1) <= &1`,
  SIMP_TAC [scale_factor_f] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [ARITH_RULE `((&1) + m)-(&1) = m`] THEN
  SUBGOAL_THEN `(&0)< ((&2) pow (fraction_length P (L:bool list) ))`
    ASSUME_TAC THENL
   [SIMP_TAC [REAL_LT_POW2]; ALL_TAC] THEN
  ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN
  SIMP_TAC [REAL_MUL_LID; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  SIMP_TAC [LE_LT] THEN DISJ1_TAC THEN
  SIMP_TAC [fraction_length; VAL_LT_EXP2]);;


let FRAC_LE_2 = prove
 (`!L P.(is_valid_posit_length P L)==>(scale_factor_f P L)<=(&2)`,
  REPEAT GEN_TAC THEN SIMP_TAC [ARITH_RULE `(&2) =(&1) +(&1)`] THEN
  SIMP_TAC [GSYM REAL_LE_SUB_RADD] THEN SIMP_TAC [FRAC_LE_1]);;


let USEED_GE_1 = prove
 (`!P. (&1)<=useed P`,
  SIMP_TAC [useed; REAL_LE_POW2]);;


let VAL_K_LE = prove
 (`!(L:bool list) . value_of_k L <= &((LENGTH L) - 2)`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [SUB_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `1<=LENGTH(t:bool list)` THENL
   [SIMP_TAC [LENGTH; value_of_k] THEN COND_CASES_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC [ADD1] THEN ASM_ARITH_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [ADD1] THEN
    SIMP_TAC
      [ARITH_RULE
         `((LENGTH (t:(bool)list) + 1) - 2) =(LENGTH (t:(bool)list) - 1)`] THEN
    ASM_SIMP_TAC [GSYM INT_OF_NUM_SUB] THENL
     [SIMP_TAC [GSYM INT_LE_SUB_LADD] THEN
      SIMP_TAC
        [ARITH_RULE
           `&(LENGTH (t:(bool)list)) - (&1:int) - (&1) =(&(LENGTH (t:(bool)list))) - (&2)`] THEN
      SUBGOAL_THEN `2<= LENGTH (t:(bool)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC [INT_OF_NUM_SUB]];
      SIMP_TAC [INT_LE_SUB_RADD] THEN
      SIMP_TAC
        [ARITH_RULE
           `&(LENGTH (t:(bool)list)) - (&1:int) + &1 = &(LENGTH (t:(bool)list))`] THEN
      ASM_ARITH_TAC];
    UNDISCH_TAC `~(1 <= LENGTH (t:(bool)list))` THEN
    SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [NOT_LE] THEN
    SIMP_TAC [ARITH_RULE `1 = SUC(0)`] THEN SIMP_TAC [LT; LENGTH_EQ_NIL] THEN
    SIMP_TAC [LENGTH; value_of_k] THEN
    SIMP_TAC [ARITH_RULE `(SUC 0 - 2) = 0`] THEN ARITH_TAC]);;


let VAL_K_LE_1 = prove
 (`!(L:bool list) . value_of_k L <= &((LENGTH L) - 1)`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [SUB_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `1<=LENGTH(t:bool list)` THENL
   [SIMP_TAC [LENGTH; value_of_k] THEN COND_CASES_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC [ADD1] THEN ASM_ARITH_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC [ADD1] THEN
      SIMP_TAC
        [ARITH_RULE
           `((LENGTH (t:(bool)list) + 1) - 1) =(LENGTH (t:(bool)list))`] THEN
      ASM_ARITH_TAC;
      SIMP_TAC [ADD1] THEN ARITH_TAC];
    UNDISCH_TAC `~(1 <= LENGTH (t:(bool)list))` THEN
    SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [NOT_LE] THEN
    SIMP_TAC [ARITH_RULE `1 = SUC(0)`] THEN SIMP_TAC [LT; LENGTH_EQ_NIL] THEN
    SIMP_TAC [LENGTH; value_of_k] THEN
    SIMP_TAC [ARITH_RULE `(SUC 0 - 2) = 0`] THEN ARITH_TAC]);;


let VAL_K_GT_0 = prove
 (`!(L:bool list) . ~(checkmax L)/\(2<=LENGTH (L))==>value_of_k L < &((LENGTH L) - 2)`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [SUB_0; checkmax; MEM] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `1<=LENGTH(t:bool list)` THENL
   [ALL_TAC;
    UNDISCH_TAC `~(1 <= LENGTH (t:(bool)list))` THEN
    SIMP_TAC [LENGTH; value_of_k] THEN SIMP_TAC [NOT_LE] THEN
    SIMP_TAC [ARITH_RULE `1 = SUC 0`] THEN SIMP_TAC [LT; LENGTH_EQ_NIL] THEN
    SIMP_TAC [LENGTH; value_of_k] THEN
    SIMP_TAC [ARITH_RULE `(SUC 0 - 2) = 0`] THEN ARITH_TAC] THEN
  SIMP_TAC [LENGTH; value_of_k] THEN REPEAT COND_CASES_TAC THENL
   [SIMP_TAC [GSYM INT_LT_SUB_LADD] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [ADD1] THEN
    SIMP_TAC
      [ARITH_RULE
         `((LENGTH (t:(bool)list) + 1) - 2) =(LENGTH (t:(bool)list))-1`] THEN
    ASM_SIMP_TAC [GSYM INT_OF_NUM_SUB] THEN
    SIMP_TAC
      [ARITH_RULE
         `(&(LENGTH (t:(bool)list)):int) - (&1) - (&1) =(&(LENGTH (t:(bool)list)):int) - (&2)`] THEN
    SUBGOAL_THEN `2 <= LENGTH (t:(bool)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [INT_OF_NUM_SUB] THEN SUBGOAL_THEN `~checkmax t` ASSUME_TAC THENL
     [ASM_MESON_TAC [CHECKMAX]; ASM_SIMP_TAC [IMP_CONJ]];
    ASM_CASES_TAC `2 <= LENGTH (t:(bool)list)` THENL
     [SIMP_TAC [ADD1] THEN
      SIMP_TAC
        [ARITH_RULE
           `((LENGTH (t:(bool)list) + 1) - 2) =(LENGTH (t:(bool)list))-1`] THEN
      ASM_SIMP_TAC [INT_OF_NUM_SUB] THEN ASM_SIMP_TAC [GSYM INT_OF_NUM_SUB] THEN
      SIMP_TAC [INT_LT_SUB_LADD] THEN SIMP_TAC [INT_ADD_LID; INT_OF_NUM_LT];
      POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [NOT_LE] THEN
      SIMP_TAC [ARITH_RULE `2 = SUC 1`; LT_SUC_LE; LE_LT] THEN
      SIMP_TAC [ARITH_RULE `1 = SUC 0`; LT] THEN SIMP_TAC [ADD1; ADD_0] THEN
      SIMP_TAC [ARITH_RULE `0+1 =1`] THEN SIMP_TAC [ARITH_RULE `1+1 =2`] THEN
      REPEAT STRIP_TAC THENL
       [ALL_TAC;
        ALL_TAC;
        ALL_TAC;
        ALL_TAC;
        ALL_TAC;
        UNDISCH_TAC `LENGTH (t:(bool)list) = 1` THEN
        SIMP_TAC [ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS] THEN
        SIMP_TAC [LENGTH_EQ_NIL] THEN SUBGOAL_THEN `~checkmax t` ASSUME_TAC THENL
         [ASM_MESON_TAC [CHECKMAX]; ALL_TAC] THEN
        POP_ASSUM MP_TAC THEN SIMP_TAC [checkmax] THEN REPEAT STRIP_TAC THEN
        UNDISCH_TAC `HD (t:(bool)list)` THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC `~checkmax (CONS (h:bool) (t:(bool)list))` THEN
        ASM_SIMP_TAC [checkmax; MEM; HD; TL]]];
    SIMP_TAC [ADD1] THEN
    SIMP_TAC
      [ARITH_RULE
         `((LENGTH (t:(bool)list) + 1) - 2) =(LENGTH (t:(bool)list))-1`] THEN
    ASM_SIMP_TAC [VAL_K_LE_1; INT_LT_ADD1; INT_LT_SUB_RADD];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

let USEED_GT_0 = prove
 (`!P.(&0)<useed P`,
  SIMP_TAC [useed; REAL_LT_POW2]);;

let REGIME_LE = prove
 (`!P L. (is_valid_posit_length P L)/\ (is_valid_posit (dest_posit P))==>
 (scale_factor_r P L) <= maxpos P`,
  REPEAT STRIP_TAC THEN SIMP_TAC [scale_factor_r; maxpos; ipow] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN SIMP_TAC [USEED_GE_1] THEN
    ASM_SIMP_TAC [VAL_K_LE; nbits_num; is_valid_posit_length] THEN
    SIMP_TAC [USEED_GE_1] THEN SIMP_TAC [GSYM INT_OF_NUM_LE] THEN
    ASM_SIMP_TAC [K_GE_0; INT_OF_NUM_OF_INT] THEN
    UNDISCH_TAC `is_valid_posit_length (P:posit) (L:(bool)list)` THEN
    SIMP_TAC [VAL_K_LE; is_valid_posit_length; nbits_num] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN STRIP_TAC THEN ASM_SIMP_TAC [VAL_K_LE];
    SIMP_TAC [GSYM INT_OF_NUM_LE] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT] THEN
    UNDISCH_TAC `is_valid_posit_length (P:posit) (L:(bool)list)` THEN
    SIMP_TAC [VAL_K_LE; is_valid_posit_length; nbits_num] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN STRIP_TAC THEN ASM_SIMP_TAC [VAL_K_LE] THEN
    SIMP_TAC [INT_LT_SUB_RADD; INT_LT_ADDR] THEN
    ONCE_REWRITE_TAC [GSYM REAL_MUL_LID] THEN ONCE_SIMP_TAC [GSYM real_div] THEN
    ONCE_SIMP_TAC [REAL_MUL_LID] THEN
    SUBGOAL_THEN
      `(&0)<useed (P:posit) pow 
num_of_int (--(value_of_k (L:(bool)list) - &1))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN SIMP_TAC [USEED_GT_0]; ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN SIMP_TAC [GSYM REAL_POW_ADD] THEN
    SIMP_TAC [USEED_GE_1] THEN ONCE_REWRITE_TAC [GSYM REAL_MUL_LID] THEN
    ONCE_SIMP_TAC [GSYM real_div] THEN ONCE_SIMP_TAC [REAL_MUL_LID] THEN
    SUBGOAL_THEN
      `(&0)<useed (P:posit) pow 
num_of_int (--value_of_k (L:(bool)list))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN SIMP_TAC [USEED_GT_0];
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN SIMP_TAC [GSYM REAL_POW_ADD] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN SIMP_TAC [USEED_GE_1]]]);;


let SCALE_REGIME_GT_0 = prove
 (`!L P.(is_valid_posit_length P L)==>(&0)<(scale_factor_r P L)`,
  REPEAT GEN_TAC THEN SIMP_TAC [scale_factor_r] THEN SIMP_TAC [USEED_GT_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IPOW_LT_0 THEN SIMP_TAC [USEED_GT_0]);;


let MAXPOS_GE_0 = prove
 (`!P.(&0<=maxpos P)`,
  SIMP_TAC [REAL_LE_LT] THEN SIMP_TAC [maxpos; REAL_POW_LT; USEED_GT_0]);;


let REGIME_LENGTH_LE = prove
 (`!(L: bool list).regime_length L <= LENGTH L - 1`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [regime_length] THEN SIMP_TAC [LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC [LENGTH; ADD1] THEN
  REWRITE_TAC
    [ARITH_RULE `(LENGTH (t:(bool)list) + 1) - 1= (LENGTH (t:(bool)list))`] THEN
  SIMP_TAC [regime_length; HD; TL] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    SIMP_TAC [LENGTH; ADD1] THEN
    REWRITE_TAC
      [ARITH_RULE `(LENGTH (t:(bool)list) + 1) - 1= (LENGTH (t:(bool)list))`] THEN
    ARITH_TAC] THEN
  COND_CASES_TAC THEN SIMP_TAC [value_of_k] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    SIMP_TAC [GSYM INT_OF_NUM_LE] THEN SIMP_TAC [GSYM INT_OF_NUM_ADD] THEN
    ASM_SIMP_TAC [INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    SIMP_TAC [GSYM INT_LE_SUB_LADD] THEN COND_CASES_TAC THENL
     [SIMP_TAC [GSYM INT_BOUNDS_LE] THEN STRIP_TAC THENL
       [POP_ASSUM MP_TAC THEN SIMP_TAC [INT_NOT_LE; INT_OF_NUM_LT] THEN
        STRIP_TAC THEN
        UNDISCH_TAC
          `abs (value_of_k (CONS (h:bool) (t:(bool)list))) <
      &(LENGTH (CONS (h:bool) (t:(bool)list))) - &2 /\
      LENGTH (CONS (h:bool) (t:(bool)list)) > 2` THEN
        ONCE_ASM_SIMP_TAC [GSYM INT_BOUNDS_LT] THEN ASM_SIMP_TAC [value_of_k] THEN
        ASM_SIMP_TAC [NOT_LE] THEN SIMP_TAC [LENGTH; ADD1] THEN ASM_ARITH_TAC;
        SIMP_TAC [INT_LE_SUB_RADD; INT_SUB_ADD] THEN
        MATCH_MP_TAC INT_LE_TRANS THEN
        EXISTS_TAC `(&(LENGTH (t:(bool)list)-2):int)` THEN STRIP_TAC THENL
         [ASM_SIMP_TAC [VAL_K_LE]; ASM_ARITH_TAC]];
      SIMP_TAC [INT_ABS_NEG; INT_ABS_NUM] THEN SIMP_TAC [INT_LE_SUB_LADD] THEN
      UNDISCH_TAC
        `abs (value_of_k (CONS (h:bool) (t:(bool)list))) <
      &(LENGTH (CONS (h:bool) (t:(bool)list))) - &2 /\
      LENGTH (CONS (h:bool) (t:(bool)list)) > 2` THEN
      SIMP_TAC [LENGTH; ADD1; INT_BOUNDS_LE; GT] THEN
      SIMP_TAC [LT_SUC_LE; GSYM ADD1] THEN ARITH_TAC];
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(&0)<=value_of_k (t:(bool)list) + &1` ASSUME_TAC THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `value_of_k (t:(bool)list)` THEN
        STRIP_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN SIMP_TAC [GSYM INT_GE] THEN
        MATCH_MP_TAC K_GE_0 THEN POP_ASSUM MP_TAC THEN SIMP_TAC [IMP_CLAUSES];
        SIMP_TAC [GSYM INT_OF_NUM_LE] THEN SIMP_TAC [GSYM INT_OF_NUM_ADD] THEN
        ASM_SIMP_TAC [INT_OF_NUM_OF_INT] THEN
        ONCE_ASM_SIMP_TAC [GSYM INT_LE_SUB_LADD] THEN
        UNDISCH_TAC
          `abs (value_of_k (CONS (h:bool) (t:(bool)list))) <
      &(LENGTH (CONS (h:bool) (t:(bool)list))) - &2 /\
      LENGTH (CONS (h:bool) (t:(bool)list)) > 2` THEN
        ONCE_ASM_SIMP_TAC [GSYM INT_BOUNDS_LT] THEN ASM_SIMP_TAC [value_of_k] THEN
        SIMP_TAC [LENGTH; ADD1] THEN ASM_ARITH_TAC];
      SIMP_TAC [NUM_OF_INT_OF_NUM] THEN SIMP_TAC [ADD] THEN
      UNDISCH_TAC
        `abs (value_of_k (CONS (h:bool) (t:(bool)list))) <
      &(LENGTH (CONS (h:bool) (t:(bool)list))) - &2 /\
      LENGTH (CONS (h:bool) (t:(bool)list)) > 2` THEN
      SIMP_TAC [LENGTH; ADD1; INT_BOUNDS_LE; GT] THEN
      SIMP_TAC [LT_SUC_LE; GSYM ADD1]];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [IMP_CLAUSES]);;


let EXP_LENGTH_EQ = prove
 (`!L P. (is_valid_posit_length P L)/\ (nbits_num P - (regime_length L +1) < ebits_num P
)==> (exp_length P L) = (nbits_num P) - ((regime_length L)+1)`,
  SIMP_TAC
    [exp_length; exp_bits; nbits_num; LENGTH; is_valid_posit_length;
     ebits_num] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [COND_CASES_TAC THEN SIMP_TAC [LENGTH_PICK_ELEM]; SIMP_TAC [LENGTH]] THEN
  ASM_ARITH_TAC);;

let EXP_LENGTH_EQ2 = prove
 (`!L P. (is_valid_posit_length P L)/\ 
(ebits_num P <= (nbits_num P - (regime_length L +1)))
==> (exp_length P L) = ebits_num P`,
  SIMP_TAC
    [exp_length; exp_bits; nbits_num; LENGTH; is_valid_posit_length;
     ebits_num] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [COND_CASES_TAC THEN SIMP_TAC [LENGTH_PICK_ELEM]; SIMP_TAC [LENGTH]] THEN
  ASM_ARITH_TAC);;

let FRAC_LENGTH = prove
 (`!L P. (is_valid_posit_length P L)==>  
(fraction_length P L = nbits_num P - (regime_length L + exp_length P L +1))`,
  SIMP_TAC [fraction_length] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [fraction_bits] THEN SIMP_TAC [COND_RAND; COND_RATOR] THEN
  COND_CASES_TAC THENL [SIMP_TAC [LENGTH_PICK_ELEM]; SIMP_TAC [LENGTH]] THEN
  ASM_ARITH_TAC);;

let EXP_REGIME_LE = prove
 (`!L P. (is_valid_posit_length P L ) ==>  
(exp_length P L) + (regime_length L) + 1 <= nbits_num P`,
  SIMP_TAC [is_valid_posit_length; exp_length] THEN SIMP_TAC [exp_bits] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [COND_CASES_TAC THEN SIMP_TAC [LENGTH; LENGTH_PICK_ELEM] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC [LENGTH; LENGTH_PICK_ELEM] THEN SIMP_TAC [ADD_CLAUSES] THEN
  ASM_SIMP_TAC
    [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_LE_SUB_LADD] THEN
  SUBGOAL_THEN `1<=(nbits_num (P:posit))` ASSUME_TAC THENL
   [SIMP_TAC [nbits_num] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2` THEN
    STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC [GSYM INT_OF_NUM_LE; FST_POSIT_NUM; IS_VALID_POSIT] THEN
    ONCE_REWRITE_TAC [POSITFORMAT_SPLIT] THEN
    SIMP_TAC [POSIT_VALID_LENGTH_GE_2; IS_VALID_POSIT];
    ASM_SIMP_TAC [REAL_OF_NUM_LE; REAL_OF_NUM_SUB] THEN
    UNDISCH_TAC `LENGTH (L:(bool)list) = nbits_num (P:posit)` THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [REGIME_LENGTH_LE]]);;


let VALID_LENGTH_CHECK = prove
 (`!L P. (is_valid_posit_length P L ) ==>  
(exp_length P L) + (regime_length L) + (fraction_length P L)+ 1 = nbits_num P`,
  SIMP_TAC [FRAC_LENGTH] THEN REPEAT STRIP_TAC THEN
  ONCE_SIMP_TAC
    [ARITH_RULE
       `exp_length (P:posit) (L:(bool)list) +
 regime_length (L:(bool)list) +
 nbits_num (P:posit) -
 (regime_length (L:(bool)list) + exp_length (P:posit) (L:(bool)list) + 1) +
 1 =  nbits_num (P:posit) -
 ( exp_length (P:posit) (L:(bool)list)+regime_length (L:(bool)list) + 1) + (exp_length (P:posit) (L:(bool)list) +
 regime_length (L:(bool)list) +1)`] THEN
  ASM_SIMP_TAC [SUB_ADD; EXP_REGIME_LE]);;


let EXP_LENGTH_NT_EQ_E = prove
 (`!L P. (is_valid_posit_length P L)/\ ((exp_length P L ) < (ebits_num P))
==> (exp_length P L) = (nbits_num P) - ((regime_length L)+1)`,
  SIMP_TAC
    [exp_length; exp_bits; is_valid_posit_length; LENGTH; LENGTH_PICK_ELEM] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  SIMP_TAC [LENGTH_PICK_ELEM; LENGTH] THEN ASM_ARITH_TAC);;


let FRAC_EQ_1 = prove
 (`!L P. (is_valid_posit_length P L)/\ exp_length (P:posit) (L:(bool)list) < ebits_num (P:posit) ==> scale_factor_f P L = (&1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [scale_factor_f] THEN
  SUBGOAL_THEN `(exp_length P L) = (nbits_num P) - ((regime_length L)+1)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [EXP_LENGTH_NT_EQ_E]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(fraction_length P L = nbits_num P - (regime_length L + exp_length P L +1))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [FRAC_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `fraction_length (P:posit) (L:(bool)list) =0` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC [fraction_length; LENGTH_EQ_NIL; BV_n] THEN ARITH_TAC);;


let FRAC_GE_0 = prove
 (`!L P. (is_valid_posit_length P L)
 ==>(&0)<= scale_factor_f P L`,
  REPEAT STRIP_TAC THEN SIMP_TAC [scale_factor_f] THEN
  SIMP_TAC [GSYM REAL_LE_LNEG] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&0)` THEN STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC [REAL_POS; REAL_LT_POW2; REAL_LE_DIV; REAL_LE_LT]);;


let FRAC_LT_2 = prove
 (`!L P.(is_valid_posit_length P L)==>(scale_factor_f P L)<(&2)`,
  REPEAT GEN_TAC THEN SIMP_TAC [scale_factor_f] THEN
  SIMP_TAC [ARITH_RULE `(&2) =(&1) +(&1)`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN SIMP_TAC [REAL_LE_REFL] THEN
  SIMP_TAC [ARITH_RULE `(&1) +(&1)= (&2)`] THEN
  ASM_SIMP_TAC
    [GSYM REAL_OF_NUM_LT; VAL_LT_EXP2; REAL_LT_LDIV_EQ; REAL_LT_POW2;
     REAL_MUL_LID; GSYM REAL_OF_NUM_POW; fraction_length] THEN
  SIMP_TAC [REAL_OF_NUM_LT; REAL_OF_NUM_POW] THEN
  SIMP_TAC [VAL_LT_EXP2; fraction_length]);;


let EXP2_LE_LEMMA = prove
 (`!m n.(1<=n)==> (2 EXP m -1) <= ((2 EXP m) * n -1 )`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `1<= 2 EXP m` ASSUME_TAC THENL
   [SIMP_TAC [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_LE_POW2];
    ALL_TAC] THEN
  ASM_SIMP_TAC [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUB; REAL_LE_SUB_RADD] THEN
  SUBGOAL_THEN `1<= 2 EXP m*n` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [ARITH_RULE `1 =1 *1`] THEN
    ASM_SIMP_TAC [LE_MULT2; LE_SUC_LT; LT_SUC_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC
    [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUB; REAL_LE_SUB_RADD;
     GSYM REAL_OF_NUM_MUL; REAL_SUB_ADD] THEN
  SIMP_TAC [GSYM REAL_OF_NUM_POW] THEN
  ONCE_REWRITE_TAC [ARITH_RULE `&2 pow m = &2 pow m*(&1)`] THEN
  SIMP_TAC [ARITH_RULE `(m*(&1))*n = m *n`] THEN
  ASM_SIMP_TAC [REAL_LE_LMUL_EQ; REAL_LT_POW2] THEN
  ASM_SIMP_TAC [REAL_OF_NUM_LE]);;

let BV_EXP_LE = prove
 (`!L P. ~((exp_length P L) < (ebits_num P))==> 
BV_n (exp_bits P L) <= (2 EXP (ebits_num P)) -1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp_length (P:posit) (L:(bool)list) = ebits_num (P:posit)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [EQ_SYM_EQ; EXP_LENGTH_NT_GE]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC [VAL_LE_EXP2; EXP_LENGTH_NT_GE; exp_length; EQ_SYM_EQ] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [] THEN STRIP_TAC THEN
  SIMP_TAC [VAL_LE_EXP2]);;


let REGIME_BITS_OF_ZERO = prove
 (`!P n. (is_valid_posit (dest_posit P)) 
 ==>(~(MEM T (get_regime_zeros (&0) P (n))))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; MEM; get_regime_zeros]; ALL_TAC] THEN
  SIMP_TAC [NOT_CLAUSES] THEN STRIP_TAC THEN
  SIMP_TAC [LENGTH; MEM; get_regime_zeros] THEN ASM_SIMP_TAC [] THEN
  SIMP_TAC [ARITH_RULE `~(&1 <= &0)`] THEN SIMP_TAC [MEM; REAL_MUL_LZERO] THEN
  ASM_ARITH_TAC);;

let REGIME_ZERO_EXCEPTION = prove
 (`!P n. (is_valid_posit (dest_posit P)) 
 ==>(zero_exception (regime_bits (&0) P))`,
  GEN_TAC THEN
  SIMP_TAC [LENGTH; MEM; get_regime_zeros; zero_exception; regime_bits] THEN
  SIMP_TAC [ARITH_RULE `~(&1 <= &0)`] THEN SIMP_TAC [REGIME_BITS_OF_ZERO]);;


let NUM_BV_MAX = prove
 (`!n. ~(MEM F (num_BV (n) ((2 EXP (n))-1)))`,
  INDUCT_TAC THEN SIMP_TAC [MEM; num_BV] THEN SIMP_TAC [DE_MORGAN_THM] THEN
  SUBGOAL_THEN `(2 EXP SUC n - 1) DIV 2 = (2 EXP n - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN
    SIMP_TAC [ARITH_RULE `1<2`] THEN SIMP_TAC [] THEN SIMP_TAC [EXP] THEN
    SIMP_TAC [ARITH_RULE `(2 EXP n - 1) * 2 = (2 *(2 EXP n)) - 2`] THEN
    SIMP_TAC [ARITH_RULE `2 * 2 EXP n - 2 + 1= 2 * 2 EXP n - 2 +2 -1`] THEN
    SUBGOAL_THEN `2 * 2 EXP n - 2 + 2 =  2 * 2 EXP n` ASSUME_TAC THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC SUB_ADD THEN ONCE_REWRITE_TAC [ARITH_RULE `2 = 2 *1`] THEN
    SIMP_TAC [ARITH_RULE `(2 * 1) * (2 * 1) EXP n =2 * 2 EXP n`] THEN
    MATCH_MP_TAC LE_MULT2 THEN
    SIMP_TAC
      [REAL_LE_REFL; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_LE_POW2];
    SUBGOAL_THEN `(2 EXP SUC n - 1) MOD 2 = 1` ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC [num2bool] THEN SIMP_TAC [ARITH_RULE `~(1=0)`]] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `((2 EXP n) - 1)` THEN
    SIMP_TAC [ARITH_RULE `1<2`] THEN SIMP_TAC [EXP] THEN
    SIMP_TAC [ARITH_RULE `(2 EXP n - 1) * 2 = (2 *(2 EXP n)) - 2`] THEN
    SIMP_TAC [ARITH_RULE `2 * 2 EXP n - 2 + 1= 2 * 2 EXP n - 2 +2 -1`] THEN
    SUBGOAL_THEN `2 * 2 EXP n - 2 + 2 =  2 * 2 EXP n` ASSUME_TAC THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC SUB_ADD THEN ONCE_REWRITE_TAC [ARITH_RULE `2 = 2 *1`] THEN
    SIMP_TAC [ARITH_RULE `(2 * 1) * (2 * 1) EXP n =2 * 2 EXP n`] THEN
    MATCH_MP_TAC LE_MULT2 THEN
    SIMP_TAC
      [REAL_LE_REFL; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_LE_POW2]]);;


let NOT_MEM_REVERSE = prove
 (`!x L. ~ (MEM x L) = ~(MEM x (REVERSE L))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP_TAC [MEM; REVERSE]; ALL_TAC] THEN
  SIMP_TAC [MEM; REVERSE; MEM_APPEND; DE_MORGAN_THM] THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [AND_CLAUSES; IMP_CLAUSES; EQ_SYM_EQ] THEN
  SIMP_TAC [CONJ_SYM]);;

let MEM_REVERSE = prove
 (`!x L.  (MEM x L) = (MEM x (REVERSE L))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP_TAC [MEM; REVERSE]; ALL_TAC] THEN
  SIMP_TAC [MEM; REVERSE; MEM_APPEND; DE_MORGAN_THM] THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [OR_CLAUSES; IMP_CLAUSES; EQ_SYM_EQ] THEN
  SIMP_TAC [DISJ_SYM]);;


let MAX_VAL_NUM_LEMMA = prove
 (`!n. ~(MEM F (num_BV_f (n) ((2 EXP (n))-1)))`,
  INDUCT_TAC THENL
   [SIMP_TAC [MEM; REVERSE; num_BV_f; num_BV];
    SIMP_TAC [num_BV_f] THEN
    ASM_MESON_TAC
      [NUM_BV_MAX; NOT_MEM_REVERSE; EQ_SYM_EQ; REVERSE_REVERSE; NUM_BV_MAX]]);;


let CHECKMAX_MAXPOS_POSIT = prove
 (`!P n. (is_valid_posit (dest_posit P)) 
 ==>(checkmax (CONS (sign_real x) (maxpos_posit P)))`,
  SIMP_TAC [checkmax; TL] THEN SIMP_TAC [maxpos_posit] THEN
  SIMP_TAC [MAX_VAL_NUM_LEMMA]);;


let ZERO_POSIT_REAL_POSIT = prove
 (`!L P x. (is_valid_posit (dest_posit P))
 /\ (is_valid_posit_length P (real_to_posit_check3 x P)) 
/\ (x=(&0))==>
add_zero_real P (real_to_posit_check3 x P) = x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [real_to_posit_check3] THEN
  SUBGOAL_THEN `(zero_exception (APPEND [F] (regime_bits (&0) P)))`
    ASSUME_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC [add_zero_real]] THEN
  SIMP_TAC [zero_exception; MEM; APPEND] THEN
  ASM_SIMP_TAC [regime_bits; ARITH_RULE `~(&1 <= &0)`; REGIME_BITS_OF_ZERO]);;


let MAXPOS_ENCODE_DECODE = prove
 (`!L P x. (is_valid_posit (dest_posit P))
 /\ (is_valid_posit_length P (real_to_posit_check3 x P))
/\ ~(zero_exception (real_to_posit_check3 (x:real) (P:posit))) 
/\ (x=(maxpos P))==>
add_zero_real P (real_to_posit_check3 x P) = x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [add_zero_real] THEN
  ASM_SIMP_TAC [real_to_posit_check3] THEN
  ASM_SIMP_TAC [real_ge; REAL_ABS_LE] THEN
  SUBGOAL_THEN `~(maxpos (P:posit)= &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC [REAL_NOT_EQ; OR_CLAUSES; MAXPOS_GT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(maxpos (P:posit) < &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC [REAL_NOT_LT; OR_CLAUSES; MAXPOS_GT_0; REAL_LE_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN COND_CASES_TAC THENL
   [POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [sign_real; sign_bit; HD]; ALL_TAC] THEN
  SUBGOAL_THEN `F = sign_real (x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN SIMP_TAC [posit_to_signed_real] THEN
  SUBGOAL_THEN `checkmax (CONS (sign_real x) (maxpos_posit P))` ASSUME_TAC THENL
   [ASM_SIMP_TAC [CHECKMAX_MAXPOS_POSIT]; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_ASM_SIMP_TAC [] THEN
  ONCE_ASM_SIMP_TAC [sign_real; sign_bit; HD] THEN
  ONCE_ASM_SIMP_TAC [sign_real; sign_bit; HD] THEN
  ONCE_ASM_SIMP_TAC [sign_real; sign_bit; HD] THEN
  ONCE_ASM_SIMP_TAC [sign_real; sign_bit; HD] THEN SIMP_TAC []);;


let REVERSE_LENGTH = prove
 (`!L. LENGTH (REVERSE L) = LENGTH L`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; REVERSE];
    ASM_SIMP_TAC [LENGTH; REVERSE; LENGTH_APPEND; ADD1] THEN ARITH_TAC]);;


let NUM_BV_LENGTH = prove
 (`!n a . LENGTH (num_BV n a) = n`,
  INDUCT_TAC THENL
   [SIMP_TAC [num_BV_f; num_BV; REVERSE; LENGTH];
    ASM_SIMP_TAC
      [LENGTH; num_BV_f; num_BV; REVERSE; APPEND; ADD1; LENGTH_APPEND]]);;


let LENGTH_NUM_BV_f = prove
 (`!n a . LENGTH (num_BV_f n a) = n`,
  INDUCT_TAC THENL
   [SIMP_TAC [num_BV_f; num_BV; REVERSE; LENGTH];
    ASM_SIMP_TAC
      [LENGTH; num_BV_f; num_BV; REVERSE; APPEND; ADD1; LENGTH_APPEND;
       NUM_BV_LENGTH; REVERSE_LENGTH] THEN
    ARITH_TAC]);;


let LEMMA1 = prove
 (`!L P x . (~ sign_bit L)/\ (checkmax L) ==> (posit_to_signed_real P L) = maxpos P`,
  ONCE_SIMP_TAC [posit_to_signed_real] THEN
  ONCE_SIMP_TAC [posit_to_signed_real] THEN ARITH_TAC);;


let SINGLETON_LIST = prove
 (`!L. LENGTH L= 1 ==> L = [HD L]`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH] THEN ARITH_TAC;
    SIMP_TAC [LENGTH; HD] THEN SIMP_TAC [SUC_INJ; ARITH_RULE `1 = SUC 0`] THEN
    SIMP_TAC [LENGTH_EQ_NIL]]);;

let SIGN_ENCODE_DECODE_POS = prove
 (`x>(&0)==> sign_bit (real_to_posit_check3 (x:real) (P:posit)) = F`,
  SIMP_TAC [sign_bit; real_to_posit_check3] THEN STRIP_TAC THEN
  REPEAT COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC [HD] THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [sign_real];
    ASM_SIMP_TAC [HD];
    ASM_SIMP_TAC [HD] THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [sign_real];
    ASM_SIMP_TAC [HD];
    ASM_SIMP_TAC [HD; APPEND];
    ASM_SIMP_TAC [HD; APPEND]] THEN
  ASM_ARITH_

let SIGN_ENCODE_DECODE_NEG = prove
 (`x<(&0)==> sign_bit (real_to_posit_check3 (x:real) (P:posit))`,
  SIMP_TAC [sign_bit; real_to_posit_check3] THEN SIMP_TAC [sign_real] THEN
  STRIP_TAC THEN SUBGOAL_THEN `~((x:real) > &0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real) = &0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REPEAT COND_CASES_TAC THENL
   [ALL_TAC; ALL_TAC; ASM_SIMP_TAC [HD; APPEND]; ASM_SIMP_TAC [HD; APPEND]] THEN
  ASM_SIMP_TAC [HD]);;


let ZERO_LIST = prove
 (`!n. ~(MEM T (num_BV n 0))`,
  INDUCT_TAC THEN SIMP_TAC [num_BV; MEM; REVERSE] THEN
  SIMP_TAC [ARITH_RULE `0 MOD 2 = 0`] THEN SIMP_TAC [num2bool] THEN
  SIMP_TAC [ARITH_RULE `0 DIV 2 = 0`] THEN ASM_SIMP_TAC []);;


let ALL_F_ZERO = prove
 (`!n. ALL(\x. (~x))(num_BV n 0)`,
  SIMP_TAC [GSYM ALL_MEM] THEN INDUCT_TAC THEN SIMP_TAC [num_BV; REVERSE] THEN
  SIMP_TAC [MEM] THEN SIMP_TAC [ARITH_RULE `0 MOD 2 = 0`] THEN
  SIMP_TAC [num2bool] THEN SIMP_TAC [ARITH_RULE `0 DIV 2 = 0`] THEN
  SIMP_TAC [MEM; DE_MORGAN_THM] THEN SIMP_TAC [MEM; DE_MORGAN_THM] THEN
  ASM_MESON_TAC []);;

let APPEND_ZERO = prove
 (`!n. APPEND (num_BV n 0) [F] = APPEND [F] (num_BV n 0)`,
  INDUCT_TAC THENL [SIMP_TAC [num_BV; APPEND]; ALL_TAC] THEN
  SIMP_TAC [num_BV; REVERSE] THEN SIMP_TAC [ARITH_RULE `0 MOD 2 = 0`] THEN
  SIMP_TAC [num2bool] THEN SIMP_TAC [ARITH_RULE `0 DIV 2 = 0`] THEN
  SIMP_TAC [APPEND] THEN ASM_SIMP_TAC [APPEND]);;


let REVERSE_ZERO = prove
 (`!n.REVERSE (num_BV n 0) = (num_BV n 0)`,
  INDUCT_TAC THENL [SIMP_TAC [num_BV; REVERSE]; ALL_TAC] THEN
  ASM_SIMP_TAC [num_BV; REVERSE] THEN SIMP_TAC [ARITH_RULE `0 MOD 2 = 0`] THEN
  SIMP_TAC [num2bool] THEN SIMP_TAC [ARITH_RULE `0 DIV 2 = 0`] THEN
  ASM_SIMP_TAC [GSYM REVERSE_APPEND; APPEND_SING; APPEND_ZERO]);;


let USEED_GE_2 = prove
 (`&2 <= useed P`,
  SIMP_TAC [useed] THEN SUBGOAL_THEN `1<= (2 EXP ebits_num P)` ASSUME_TAC THENL
   [SIMP_TAC [GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC [REAL_LE_POW2];
    ONCE_REWRITE_TAC [ARITH_RULE `(&2 = (&2 pow 1))`] THEN
    ONCE_REWRITE_TAC
      [ARITH_RULE
         `(&2 pow 1 pow (2 EXP ebits_num P))= &2  pow (2 EXP ebits_num P)`] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_ARITH_TAC]);;


let POW_0 = prove
 (`!n.  (x pow n = (&1)) ==> ((abs x = &1) \/ n=0)`,
  ASM_SIMP_TAC [REAL_POW_EQ_1] THEN ARITH_TAC);;


let LEMMA2 = prove
 (`sign_bit L /\ checkmax L ==> posit_to_signed_real P L = --minpos P`,
  ONCE_SIMP_TAC [posit_to_signed_real; minpos] THEN
  ONCE_SIMP_TAC [posit_to_signed_real; minpos] THEN ARITH_TAC);;


let NOT_APPEND_SYM = prove
 (`!l m. not_0(APPEND l m) = APPEND (not_0 l) (not_0 m)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC [APPEND; not_0]);;


let LAST_F_EVEN = prove
 (`!L. (BV_n (APPEND L [F])) MOD 2 = 0`,
  LIST_INDUCT_TAC THEN SIMP_TAC [APPEND; BV_n; BV; LENGTH] THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(2=0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SIMP_TAC [ARITH_RULE `m*1 = m`] THEN SIMP_TAC [GSYM EVEN_MOD] THEN
    ASM_SIMP_TAC [EVEN_ADD] THEN REWRITE_TAC [EVEN_EXP; EVEN_MOD] THEN
    ASM_SIMP_TAC [LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC [ARITH_RULE `m*0 = 0`] THEN
    ASM_SIMP_TAC [ARITH_RULE `0+m = m`]]);;

let SUC_BV_n_ODD = prove
 (`!L. (SUC (BV_n (APPEND L [F])) MOD 2) = 1`,
  SIMP_TAC [GSYM ODD_MOD] THEN SIMP_TAC [ODD; NOT_ODD] THEN
  SIMP_TAC [EVEN_MOD; LAST_F_EVEN]);;


let SUPP_THM = prove
 (`!L . (~MEM F L)==>(SUC (BV_n (APPEND L [F])))  = ((2 EXP (LENGTH L +1)) -1)`,
  LIST_INDUCT_TAC THEN SIMP_TAC [BV_n; APPEND; SUB_0; LENGTH; MEM; BV] THENL
   [ASM_SIMP_TAC [ARITH_RULE `m*0 = 0`];
    SIMP_TAC [MEM; DE_MORGAN_THM] THEN SIMP_TAC [ARITH_RULE `m*1 = m`] THEN
    SIMP_TAC [LENGTH_APPEND; LENGTH] THEN ASM_SIMP_TAC [GSYM ADD_SUC] THEN
    ASM_SIMP_TAC [ARITH_RULE `(m+1)-1 = m`] THEN
    SIMP_TAC [ADD1; ADD_0; ADD_SYM] THEN
    SIMP_TAC [ARITH_RULE `m-1+m = m+m-1`] THEN SIMP_TAC [EXP_ADD] THEN
    SIMP_TAC [ARITH_RULE `2 EXP 1 = 2`; GSYM MULT_2]] THEN
  ARITH_TAC);;

let NOT_OF_ZERO = prove
 (`!n. ~(MEM F (not_0 (num_BV n 0)))`,
  INDUCT_TAC THEN
  SIMP_TAC [num_BV_f; num_BV; BV_n; not_0; REVERSE; LENGTH; MEM] THEN
  SIMP_TAC [ARITH_RULE `1 MOD 2 = 1`] THEN SIMP_TAC [num2bool; REVERSE] THEN
  SIMP_TAC [ARITH_RULE `1 DIV 2 = 0`] THEN ASM_ARITH_TAC);;


let LENGTH_NEG = prove
 (`!L. LENGTH (not_0 L) = LENGTH L`,
  LIST_INDUCT_TAC THEN SIMP_TAC [LENGTH; not_0] THEN ASM_ARITH_TAC);;


let SUB2_DIV = prove
 (`(0<n)==> ((2*n) -1) DIV 2 = n-1`,
  ARITH_TAC);;

let CHECKMAX_TWO_COMPLEMENT = prove
 (`!n. ~(MEM F (two_complement (num_BV_f (n) (1))))`,
  INDUCT_TAC THENL
   [SIMP_TAC [two_complement] THEN
    SIMP_TAC [num_BV_f; num_BV; BV_n; not_0; REVERSE; LENGTH; MEM];
    ALL_TAC] THEN
  SIMP_TAC [num_BV_f; num_BV; BV_n; not_0; REVERSE; LENGTH; MEM] THEN
  SIMP_TAC [ARITH_RULE `1 MOD 2 = 1`] THEN
  SIMP_TAC [ARITH_RULE `1 DIV 2 = 0`] THEN SIMP_TAC [num2bool; REVERSE] THEN
  SIMP_TAC [ARITH_RULE `~(1=0)`] THEN SIMP_TAC [two_complement] THEN
  SIMP_TAC [MEM_APPEND; LENGTH_APPEND; REVERSE_APPEND; REVERSE_LENGTH] THEN
  SIMP_TAC [NUM_BV_LENGTH; LENGTH] THEN
  ASM_SIMP_TAC [REVERSE_ZERO; NOT_APPEND_SYM; not_0] THEN
  SIMP_TAC [GSYM ADD1; GSYM ONE] THEN SIMP_TAC [num_BV_f; num_BV; MEM] THEN
  SIMP_TAC [GSYM MEM_REVERSE; MEM] THEN SIMP_TAC [DE_MORGAN_THM] THEN
  ASM_SIMP_TAC [SUC_BV_n_ODD] THEN SIMP_TAC [num2bool] THEN
  SIMP_TAC [ARITH_RULE `~(1=0)`] THEN SIMP_TAC [SUPP_THM; NOT_OF_ZERO] THEN
  SIMP_TAC [LENGTH_NEG; NUM_BV_LENGTH] THEN SIMP_TAC [EXP_ADD] THEN
  SIMP_TAC [ARITH_RULE `2 EXP 1 = 2`] THEN
  SIMP_TAC [ARITH_RULE `2 EXP n *2 = 2*2 EXP n`] THEN
  SUBGOAL_THEN `0< 2 EXP n` ASSUME_TAC THENL
   [SIMP_TAC [GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC [REAL_LT_POW2];
    ASM_SIMP_TAC [LT_POW2_REFL; SUB2_DIV] THEN SIMP_TAC [NUM_BV_MAX]]);;


let CHECKMAX_NEG = prove
 (`! x P .checkmax (CONS (sign_real x) (two_complement (minpos_posit P)))`,
  SIMP_TAC [checkmax; minpos_posit; TL; CHECKMAX_TWO_COMPLEMENT]);;


let ABS_1 = prove
 (`abs (&1) = &1`,
  ARITH_TAC);;

let GT_NEG_MINPOS = prove
 (`!L P x. (x<(&0)) /\
(is_valid_posit (dest_posit P)) /\ 
(is_valid_posit_length P (real_to_posit_check3 x P)) /\
~(zero_exception (real_to_posit_check3 x P)) /\
~( inf_exception (real_to_posit_check3 x P) ) /\
((x:real) >= --minpos (P:posit)) ==>
 add_zero_real P (real_to_posit_check3 x P) = --(minpos P)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x=(&0))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [add_zero_real] THEN ASM_SIMP_TAC [real_to_posit_check3] THEN
  ASM_SIMP_TAC [sign_real] THEN SUBGOAL_THEN `abs x <= minpos P` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LEMMA2 THEN SIMP_TAC [HD; sign_bit; minpos] THEN
    SUBGOAL_THEN `T = sign_real x` ASSUME_TAC THENL
     [ASM_SIMP_TAC [sign_real];
      ASM_SIMP_TAC [CHECKMAX_NEG] THEN ASM_ARITH_TAC]] THEN
  SUBGOAL_THEN `maxpos P = (&1)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC [real_ge; GSYM IMP_CONJ; minpos] THEN SIMP_TAC [CONJ_SYM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `maxpos P <= (&1)/ (maxpos P)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC [REAL_LE_RDIV_EQ; MAXPOS_GT_0; GSYM REAL_POW_2] THEN
    ONCE_REWRITE_TAC [ARITH_RULE `(&1) = (&1) pow 2`] THEN
    SIMP_TAC [GSYM REAL_LE_SQUARE_ABS; ABS_1; real_abs] THEN
    SIMP_TAC [REAL_LE_LT; MAXPOS_GT_0] THEN
    ONCE_REWRITE_TAC [ARITH_RULE `(&1) pow 2 = (&1)`] THEN
    SUBGOAL_THEN `~(maxpos P < &1)` ASSUME_TAC THENL
     [SIMP_TAC [REAL_NOT_LT; MAXPOS_GE_1]; ASM_SIMP_TAC []];
    SUBGOAL_THEN `nbits_num P = 2` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN SIMP_TAC [maxpos] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(abs (useed P) = &1)\/ (nbits_num P - 2 = 0)` ASSUME_TAC THENL
       [ASM_SIMP_TAC [POW_0]; ALL_TAC] THEN
      SUBGOAL_THEN `~(abs (useed P) = &1)` ASSUME_TAC THENL
       [SIMP_TAC [REAL_NOT_EQ] THEN DISJ2_TAC THEN
        ASM_SIMP_TAC [real_abs; USEED_GT_0; REAL_LE_LT] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&2)` THEN STRIP_TAC THENL
         [ARITH_TAC; ASM_SIMP_TAC [USEED_GE_2]];
        POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [SUB_EQ_0] THEN
        REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `nbits_num P <= 2` THEN SIMP_TAC [LE_LT] THEN
        REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(nbits_num P < 2)` ASSUME_TAC THENL
         [SIMP_TAC [NOT_LT; NBITS_GE_2]; ASM_ARITH_TAC]];
      MATCH_MP_TAC LEMMA2 THEN
      ASM_SIMP_TAC [sign_bit; checkmax; TL; HD; maxpos_posit] THEN
      SIMP_TAC [ARITH_RULE `2-1 = 1`] THEN
      SIMP_TAC [ARITH_RULE `2 EXP 1 = 2`] THEN
      SIMP_TAC [ARITH_RULE `2-1 = 1`] THEN SIMP_TAC [CHECKMAX_TWO_COMPLEMENT]]]);;


let BV_SING_ELEM = prove
 (`!L. BV_n (APPEND L [m:bool]) = if ~m then (2*(BV_n L)) else ((2*(BV_n L)) +1)`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [BV_n; BV] THEN SIMP_TAC [LENGTH; APPEND; APPEND_NIL; BV_n; BV] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `APPEND (CONS (h:bool) (t:(bool)list)) [(m:bool)] = APPEND [(h:bool)](APPEND (t:(bool)list) [(m:bool)])`
    ASSUME_TAC THENL
   [SIMP_TAC [SINGLETON_LIST; APPEND; APPEND_SING; APPEND_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC [APPEND_SING] THEN SIMP_TAC [LENGTH; APPEND; APPEND_NIL; BV_n] THEN
  ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN SIMP_TAC [] THEN
  ASM_SIMP_TAC [LENGTH_APPEND; LENGTH; EXP; MULT_CLAUSES] THEN
  SIMP_TAC [GSYM ONE; GSYM ADD1; EXP] THEN ASM_ARITH_TAC);; 



let BV_REVERSE_NUM_BV = prove
 (`!n a. (a< 2 EXP n)==>  BV_n (REVERSE (num_BV (n:num) (a:num))) = a`,
  INDUCT_TAC THEN SIMP_TAC [BV_n; num_BV_f; REVERSE; num_BV] THENL
   [SIMP_TAC [EXP; ADD; LT; ONE; ADD_SYM]; ALL_TAC] THEN
  SIMP_TAC [BV_SING_ELEM; EXP] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((a:num) DIV 2) < 2 EXP (n:num)` ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
      `BV_n (REVERSE (num_BV (n:num) ((a:num) DIV 2))) = ((a:num) DIV 2)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC `((a:num) DIV 2)`);
      SIMP_TAC [num2bool] THEN COND_CASES_TAC THEN ASM_SIMP_TAC []]] THEN
  ASM_ARITH_TAC);;


let BV_NUM_BV = prove
 (`!n. (a< 2 EXP n)==>BV_n (num_BV_f n a ) = a`,
  INDUCT_TAC THEN SIMP_TAC [BV_n; num_BV_f; REVERSE; num_BV] THENL
   [SIMP_TAC [EXP; ADD; LT; ONE; ADD_SYM]; ALL_TAC] THEN
  SIMP_TAC [BV_SING_ELEM; EXP] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((a:num) DIV 2) < 2 EXP (n:num)` ASSUME_TAC THENL
   [ALL_TAC;
    SIMP_TAC [num2bool] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [BV_REVERSE_NUM_BV]] THEN
  ASM_ARITH_TAC);;

let REAL_POW_EQ2 = prove
 (`(m=n) ==> x pow m = x pow n`,
  STRIP_TAC THEN ASM_REWRITE_TAC [REAL_POW_EQ_EQ] THEN ARITH_TAC);;

let LIST_EQ = prove
 (`!L M. (L = M) ==> (BV_n L = BV_n M)`,
  LIST_INDUCT_TAC THEN SIMP_TAC [BV_n; BV; EQ_SYM_EQ]);;


let SIGN_REAL_DECODE = prove
 (`x>(&0) ==> sign_real x = F`,
  SIMP_TAC [sign_real] THEN ARITH_TAC);;

let FIRST_LIST_APPEND = prove
 (`! (A:bool list) (B:bool list) . (0< LENGTH A)==>
pick_elements_simp (APPEND A B)(0) (LENGTH A)= A`,
  LIST_INDUCT_TAC THENL [SIMP_TAC [LENGTH; LT_REFL]; ALL_TAC] THEN
  SIMP_TAC [LENGTH; pick_elements_simp] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [EL; HD; APPEND; GSYM ADD1; L_ADD1; TL] THEN
  ASM_CASES_TAC `0 < (LENGTH (t:(bool)list))` THENL
   [ASM_SIMP_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC
    [NOT_LT; LE_LT; LT; LENGTH_EQ_NIL; APPEND_NIL; LENGTH; pick_elements_simp]);;


let THRD_LIST_APPEND = prove
 (`! (A:bool list) (B:bool list) . (0<LENGTH B)==>
pick_elements_simp (APPEND A (APPEND B C))(LENGTH A) (LENGTH B) = B`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; APPEND; FIRST_LIST_APPEND]; ALL_TAC] THEN
  SIMP_TAC [LENGTH; pick_elements_simp] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [EL; HD; APPEND; GSYM ADD1; L_ADD1; TL]);;


let PICK_LIST_APPEND3 = prove
 (`! (A:bool list) (B:bool list) (C:bool list). (0<LENGTH B)==>
pick_elements (APPEND A (APPEND B C)) (LENGTH A)((LENGTH(A))+(LENGTH B ) -1)= B`,
  SIMP_TAC [pick_elements] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `((LENGTH (A:(bool)list) + LENGTH (B:(bool)list) - 1) - LENGTH (A:(bool)list) +
  1) = LENGTH B`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_MESON_TAC [THRD_LIST_APPEND]]);;



let PICK_LIST_APPEND4 = prove
 (`! (A:bool list) (B:bool list) (C:bool list). (0<LENGTH B)/\(0<LENGTH C)==>
pick_elements(APPEND A (APPEND B C)) ((LENGTH(A))+(LENGTH B))((LENGTH(A))+(LENGTH B)+ (LENGTH C) -1)= C`,
  SIMP_TAC [pick_elements] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `((LENGTH (A:(bool)list) + LENGTH (B:(bool)list) + LENGTH (C:(bool)list) - 1) - (LENGTH (A:(bool)list)+ LENGTH (B:(bool)list)) +
  1) = LENGTH C`
    ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC [SND_LIST_APPEND; APPEND_ASSOC; GSYM LENGTH_APPEND]);;

v

let LENGTH_FRAC = prove
 (`!n x.LENGTH (fraction_list x n ) = n`,
  INDUCT_TAC THEN SIMP_TAC [fraction_list; LENGTH] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN SIMP_TAC [LENGTH] THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `(&2 * (x:real) - &1)`);
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real)* (&2))`)] THEN
  ARITH_TAC);;



let K_OF_APPEND = prove
 (`!(A:bool list)(B:bool list)(C:bool list)(s:bool).((EL ((LENGTH A)-1 ) A = ~(EL ((LENGTH A) - 2) A)))/\
 (1< LENGTH A)==>
value_of_k (CONS s (APPEND A (APPEND B C))) = value_of_k  (CONS s A)`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC [LENGTH; LT_REFL; ARITH_RULE `~(1<0)`]; ALL_TAC] THEN
  SIMP_TAC [LENGTH; EL_TL; EL_CONS] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(SUC (LENGTH (t:(bool)list)) - 1 = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
    `(if SUC (LENGTH (t:(bool)list)) - 1 = 0
       then (h:bool)
       else EL (SUC (LENGTH (t:(bool)list)) - 1 - 1) (t:(bool)list)) <=>
      ~(if SUC (LENGTH (t:(bool)list)) - 2 = 0
        then (h:bool)
        else EL (SUC (LENGTH (t:(bool)list)) - 2 - 1) (t:(bool)list))` THEN
  ASM_SIMP_TAC [] THEN ASM_CASES_TAC `1 < LENGTH (t:(bool)list)` THENL
   [SUBGOAL_THEN `~( SUC (LENGTH (t:(bool)list)) - 2 = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `(SUC (LENGTH (t:(bool)list)) - 1 - 1) = (LENGTH (t:(bool)list) - 1)`
      ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `(SUC (LENGTH (t:(bool)list)) - 2 - 1)= (LENGTH (t:(bool)list) - 2)`
      ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [value_of_k] THEN
    ASM_SIMP_TAC [APPEND] THEN
    ASM_SIMP_TAC [HD; TL; APPEND; APPEND_ASSOC; LENGTH] THEN
    ASM_SIMP_TAC [NOT_LE; HD_APPEND] THEN
    SUBGOAL_THEN `~( APPEND (t:bool list) B = [])` ASSUME_TAC THENL
     [ASM_SIMP_TAC [APPEND_EQ_NIL; DE_MORGAN_THM] THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `1 < SUC (LENGTH (APPEND (APPEND (t:bool list) B) C))`
        ASSUME_TAC THENL
       [ASM_SIMP_TAC [LENGTH_APPEND; ADD1] THEN ASM_SIMP_TAC [LT_ADDR];
        ASM_SIMP_TAC [] THEN DISJ1_TAC THEN
        ASM_SIMP_TAC [GSYM LENGTH_EQ_NIL; GSYM LT_NZ]] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC [] THEN SUBGOAL_THEN `~((t:bool list)=[])` ASSUME_TAC THENL
       [ASM_SIMP_TAC [GSYM LENGTH_EQ_NIL; GSYM LT_NZ] THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `1 < SUC (LENGTH (APPEND (APPEND (t:bool list) B) C))`
          ASSUME_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC []] THEN
        ASM_SIMP_TAC [LENGTH_APPEND; ADD1] THEN ASM_SIMP_TAC [LT_ADDR] THEN
        ASM_ARITH_TAC]];
    SUBGOAL_THEN `(LENGTH (t:(bool)list) = 1)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `SUC (LENGTH (t:(bool)list)) - 2 = 0` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN SUBGOAL_THEN `(SUC 1 - 1 - 1)= 0` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [EL] THEN STRIP_TAC THEN ASM_SIMP_TAC [APPEND] THEN
    ASM_SIMP_TAC [value_of_k] THEN
    SUBGOAL_THEN `~((t:bool list)=[])` ASSUME_TAC THENL
     [ASM_SIMP_TAC [GSYM LENGTH_EQ_NIL; GSYM LT_NZ] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [HD; TL] THEN
      ASM_SIMP_TAC [HD; TL; HD_APPEND]]]);;



let LENGTH_TWO_COMP = prove
 (`!L. LENGTH(two_complement L) = LENGTH L`,
  LIST_INDUCT_TAC THEN SIMP_TAC [two_complement] THEN
  SIMP_TAC
    [num_BV_f; num_BV; LENGTH; BV_n; not_0; REVERSE; REVERSE_LENGTH;
     LENGTH_NUM_BV_f]);;


let K_SAME = prove
 (`!(L:bool list). value_of_k (CONS T L) = value_of_k (CONS F L)`,
  SIMP_TAC [value_of_k]);;


let LEMMA3 = prove
 (`!(x:real) y z. x - (y+z) = x-y-z`,
  ARITH_TAC);;


let FRAC_RESIDUE_FIXED_VAL = prove
 (`! n x y. (fraction_residue1 x n= y)==> (((x:real) -
(&(BV_n (fraction_list (x:real) (n:num))) /
             &2 pow LENGTH (fraction_list (x:real) (n:num))))*(&2 pow n))= y`,
  INDUCT_TAC THEN SIMP_TAC [fraction_residue1; fraction_list; BV_n] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN SIMP_TAC [] THEN
  SIMP_TAC [BV_n; BV; MULT_CLAUSES; ADD_CLAUSES] THEN
  SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
  SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `(&2 * (x:real) - &1)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow] THEN
    ASM_SIMP_TAC [GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC [LEMMA3] THEN MESON_TAC [REAL_POLY_CLAUSES; REAL_MUL_ASSOC];
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) * &2)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow]]);;



let FRAC_RESIDUE_FIXED_LT = prove
 (`! n x y. (fraction_residue1 x n< y)==> (((x:real) -
(&(BV_n (fraction_list (x:real) (n:num))) /
             &2 pow LENGTH (fraction_list (x:real) (n:num))))*(&2 pow n))< y`,
  INDUCT_TAC THEN SIMP_TAC [fraction_residue1; fraction_list; BV_n] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN SIMP_TAC [] THEN
  SIMP_TAC [BV_n; BV; MULT_CLAUSES; ADD_CLAUSES] THEN
  SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
  SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `(&2 * (x:real) - &1)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow] THEN
    ASM_SIMP_TAC [GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC [LEMMA3] THEN MESON_TAC [REAL_POLY_CLAUSES; REAL_MUL_ASSOC];
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) * &2)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow]]);;



let FRAC_RESIDUE_FIXED_GT = prove
 (`! n x y. (fraction_residue1 x n> y)==> (((x:real) -
(&(BV_n (fraction_list (x:real) (n:num))) /
             &2 pow LENGTH (fraction_list (x:real) (n:num))))*(&2 pow n))> y`,
  INDUCT_TAC THEN SIMP_TAC [fraction_residue1; fraction_list; BV_n] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN SIMP_TAC [] THEN
  SIMP_TAC [BV_n; BV; MULT_CLAUSES; ADD_CLAUSES] THEN
  SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
  SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `(&2 * (x:real) - &1)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow] THEN
    ASM_SIMP_TAC [GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC [LEMMA3] THEN MESON_TAC [REAL_POLY_CLAUSES; REAL_MUL_ASSOC];
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) * &2)`) THEN
    SIMP_TAC [LENGTH; LENGTH_FRAC] THEN ASM_SIMP_TAC [REAL_SUB_RDISTRIB] THEN
    SIMP_TAC [REAL_DIV_RMUL; REAL_LT_POW2; REAL_NOT_EQ] THEN
    SIMP_TAC [REAL_MUL_ASSOC; real_pow]]);;


let RESIDUE_OF_ZERO = prove
 (`! n x. fraction_residue1 (&0) (n:num) = &0`,
  INDUCT_TAC THEN SIMP_TAC [fraction_residue1; fraction_list] THEN
  ASM_SIMP_TAC [REAL_MUL_LZERO] THEN ARITH_TAC);;


let FRAC_RESIDUE_POS = prove
 (`! n x . ((&0)<=x)==>(~(fraction_residue1 x n < (&0)))`,
  INDUCT_TAC THEN SIMP_TAC [fraction_residue1; fraction_list] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) * &2)`) THEN ASM_ARITH_TAC] THEN
  SIMP_TAC [] THEN FIRST_X_ASSUM (MP_TAC o SPEC `(&2 * (x:real) - &1)`) THEN
  ASM_SIMP_TAC [REAL_SUB_LT] THEN POP_ASSUM MP_TAC THEN SIMP_TAC [REAL_LE_LT] THEN
  STRIP_TAC THENL
   [SIMP_TAC [] THEN ASM_ARITH_TAC;
    POP_ASSUM MP_TAC THEN
    SIMP_TAC [EQ_SYM_EQ; REAL_MUL_AC; REAL_LT_REFL; REAL_SUB_REFL]]);;


let EXP_VALUE_BOUND = prove
 (`!n x. exp_bits_value x n <= n`,
  INDUCT_TAC THENL [SIMP_TAC [exp_bits_value; LE_REFL]; ALL_TAC] THEN
  SIMP_TAC [exp_bits_value] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) / &2)`) THEN SIMP_TAC [ADD1]] THEN
  ARITH_TAC);;


let POW_OF_EXP_VAL = prove
 (`!n x. &1 <= (x:real)==> &2 pow exp_bits_value x n <= x`,
  INDUCT_TAC THENL [SIMP_TAC [exp_bits_value; real_pow]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC [exp_bits_value; real_pow] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) / &2)`) THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC [real_pow];
    ASM_SIMP_TAC [REAL_POW_ADD; REAL_POW_1] THEN ASM_ARITH_TAC]);;


let NUM_OF_INT_ADD = prove
 (`!(a:int) (b:int). (&0 <= a)/\(&0 <= b)==>num_of_int(a + b) = num_of_int (a) + num_of_int(b)`,
  ASM_SIMP_TAC [GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC [INT_OF_NUM_OF_INT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0<=((a:int) + (b:int))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC [INT_OF_NUM_OF_INT]]);;



 let USEED_POW_ONES = prove
 (`!n x.  (&1 <= (x:real)) ==> (useed P) pow num_of_int (value_of_k (APPEND [sign_real (x:real)]
(get_regime_ones x P n))) <= x`,
  INDUCT_TAC THEN
  SIMP_TAC [get_regime_ones; value_of_k; APPEND_SING; HD; LENGTH; LE_REFL] THENL
   [ASM_SIMP_TAC [ARITH_RULE `(0 <= 1)`] THEN
    ASM_SIMP_TAC [ARITH_RULE `(SUC 0 <= 1)`] THEN
    ASM_SIMP_TAC [real_pow; NUM_OF_INT_OF_NUM];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THENL
   [SIMP_TAC [value_of_k] THEN ASM_SIMP_TAC [HD; TL; LENGTH] THEN
    SIMP_TAC [ONE; LE_REFL];
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) / useed (P:posit))`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `num_of_int
 (value_of_k
  (CONS T (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num))) +
  &1)  = num_of_int
 (value_of_k
  (CONS T (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))) +
  1`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `1 = num_of_int(&1)` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [NUM_OF_INT_OF_NUM];
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN `&(num_of_int(&1)) = (&1:int)` ASSUME_TAC THENL
       [ASM_MESON_TAC [INT_OF_NUM_OF_INT]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC NUM_OF_INT_ADD THEN STRIP_TAC THENL
       [ALL_TAC; ARITH_TAC] THEN
      SIMP_TAC [] THEN ASM_MESON_TAC [K_GE_0; GSYM INT_GE];
      UNDISCH_TAC
        `HD
      (TL
      (if (x:real) < useed (P:posit)
       then [T; F]
       else CONS T
            (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))) /\
      ~(LENGTH
        (if (x:real) < useed (P:posit)
         then [T; F]
         else CONS T
              (get_regime_ones ((x:real) / useed (P:posit)) (P:posit)
              (n:num))) <=
        1)` THEN
      ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [K_SAME] THEN
      ASM_SIMP_TAC [REAL_POW_ADD; REAL_POW_1] THEN
      ASM_SIMP_TAC [GSYM REAL_LE_RDIV_EQ; USEED_GT_0] THEN
      UNDISCH_TAC
        `&1 <= (x:real) / useed (P:posit)
      ==> useed (P:posit) pow
          num_of_int
          (value_of_k
          (APPEND [sign_real ((x:real) / useed (P:posit))]
          (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))) <=
          (x:real) / useed (P:posit)` THEN
      ASM_SIMP_TAC [sign_real] THEN
      SUBGOAL_THEN `~((x:real) / useed (P:posit) < &0)` ASSUME_TAC THENL
       [ASM_SIMP_TAC [REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_SIMP_TAC [REAL_LE_LT; USEED_GT_0];
        ASM_SIMP_TAC [APPEND_SING] THEN
        ASM_SIMP_TAC [REAL_LE_RDIV_EQ; USEED_GT_0]] THEN
      ASM_ARITH_TAC];
    ALL_TAC;
    SIMP_TAC [value_of_k] THEN ASM_SIMP_TAC [HD; TL; LENGTH] THEN
    SIMP_TAC [ONE; LE_REFL] THEN
    ASM_SIMP_TAC
      [NUM_OF_INT_OF_NUM; INT_ADD_LINV; ADD1; REAL_OF_NUM_ADD; ADD_CLAUSES;
       real_pow] THEN
    UNDISCH_TAC
      `~HD
       (if (x:real) < useed (P:posit)
        then [T; F]
        else CONS T
             (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))` THEN
    SIMP_TAC [COND_RAND; HD] THEN ASM_ARITH_TAC;
    UNDISCH_TAC
      `~HD
       (if (x:real) < useed (P:posit)
        then [T; F]
        else CONS T
             (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))` THEN
    ASM_SIMP_TAC [COND_RAND; HD];
    UNDISCH_TAC
      `~HD
       (if (x:real) < useed (P:posit)
        then [T; F]
        else CONS T
             (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))` THEN
    ASM_SIMP_TAC [COND_RAND; HD] THEN ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC
    [NUM_OF_INT_OF_NUM; INT_ADD_LINV; ADD1; REAL_OF_NUM_ADD; ADD_CLAUSES;
     real_pow]);;


 	 let K_NEG_ZEROS = prove
 (`!n x. (&0< x)==> ~(&0 < value_of_k (APPEND  [sign_real (x:real)] 
(get_regime_zeros (x:real) (P:posit) (n))))`,
  INDUCT_TAC THEN ASM_SIMP_TAC [get_regime_zeros] THENL
   [SIMP_TAC [REAL_LT_IMP_NZ] THEN SIMP_TAC [value_of_k; APPEND_SING] THEN
    SIMP_TAC [HD; TL; LENGTH] THEN ASM_SIMP_TAC [ARITH_RULE `(SUC 0 <= 1)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [SIMP_TAC [value_of_k; APPEND_SING] THEN SIMP_TAC [HD; TL; LENGTH] THEN
    ASM_SIMP_TAC [ARITH_RULE `(SUC 0 <= 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) * useed (P:posit))`) THEN STRIP_TAC THEN
  SIMP_TAC [value_of_k; APPEND_SING] THEN SIMP_TAC [HD; TL; LENGTH] THEN
  COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN COND_CASES_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  UNDISCH_TAC
    `&0 < (x:real) * useed (P:posit)
      ==> ~(&0 <
            value_of_k
            (APPEND [sign_real ((x:real) * useed (P:posit))]
            (get_regime_zeros ((x:real) * useed (P:posit)) (P:posit) (n:num))))` THEN
  ASM_SIMP_TAC [value_of_k; APPEND_SING] THEN ASM_SIMP_TAC [HD; TL; LENGTH] THEN
  ASM_SIMP_TAC [INT_NOT_LT; INT_LE_SUB_RADD] THEN
  SUBGOAL_THEN `&0 < (x:real) * useed (P:posit)` ASSUME_TAC THENL
   [ASM_MESON_TAC [REAL_LT_MUL; USEED_GT_0]; ASM_ARITH_TAC]);;



let K_POS_ONES =prove
 (`!n x . (&0< x)==> (&0 <=
        value_of_k
        (APPEND [sign_real (x:real)]
        (get_regime_ones (x:real) (P:posit) (n))))`,
  INDUCT_TAC THEN ASM_SIMP_TAC [get_regime_ones] THENL
   [SIMP_TAC [REAL_LT_IMP_NZ] THEN SIMP_TAC [value_of_k; APPEND_SING] THEN
    SIMP_TAC [HD; TL; LENGTH] THEN ASM_SIMP_TAC [ARITH_RULE `(SUC 0 <= 1)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SIMP_TAC [value_of_k; APPEND_SING] THEN ASM_SIMP_TAC [LENGTH] THEN
    ASM_SIMP_TAC [ARITH_RULE `(SUC 0 <= 1)`] THEN SIMP_TAC [HD] THEN
    SIMP_TAC [HD; TL] THEN SIMP_TAC [INT_LE_REFL];
    FIRST_X_ASSUM (MP_TAC o SPEC `((x:real) / useed (P:posit))`) THEN
    STRIP_TAC THEN SIMP_TAC [value_of_k; APPEND_SING] THEN
    SIMP_TAC [HD; TL; LENGTH] THEN COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    UNDISCH_TAC
      `&0 < (x:real) / useed (P:posit)
      ==> &0 <=
          value_of_k
          (APPEND [sign_real ((x:real) / useed (P:posit))]
          (get_regime_ones ((x:real) / useed (P:posit)) (P:posit) (n:num)))` THEN
    ASM_SIMP_TAC [value_of_k; APPEND_SING] THEN ASM_SIMP_TAC [HD; TL; LENGTH] THEN
    ASM_SIMP_TAC [INT_NOT_LT; INT_LE_SUB_RADD] THEN
    SUBGOAL_THEN `&0 < (x:real) / useed (P:posit)` ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LT_DIV; USEED_GT_0]; ASM_ARITH_TAC]]);;
	 
	 (*_________________________________not in then/thenl form _____________________________________*)
	 
g`!L P .(is_valid_posit (dest_posit P)) /\ (is_valid_posit_length P L) /\
~( zero_exception L) /\
~( inf_exception L ) ==>( posit_to_signed_real P L <= maxpos P)`;;
e(SIMP_TAC[posit_to_signed_real]);;
e(REPEAT STRIP_TAC);;
e(COND_CASES_TAC);;
e(COND_CASES_TAC);;
e(SIMP_TAC[NEG_RECIPROCAL_LE;MAXPOS_GE_1]);;
e(ARITH_TAC);;
e(COND_CASES_TAC);;
e(ASM_SIMP_TAC[REAL_LE_LNEG;REAL_LE_ADD]);;
e(MATCH_MP_TAC REAL_LE_ADD );;
e(SIMP_TAC[MAXPOS_GE_0]);;
e(SIMP_TAC[REAL_MUL_POS_LE]);;
e(REPEAT STRIP_TAC);;
e(DISJ2_TAC);;
e(DISJ2_TAC);;
e(DISJ1_TAC);;
e(REPEAT STRIP_TAC);;
e(SIMP_TAC[scale_factor_r;useed;IPOW_LT_0]);;
e(COND_CASES_TAC);;
 e(MATCH_MP_TAC IPOW_LT_0);;
e(SIMP_TAC[REAL_LT_POW2]);;
 e(MATCH_MP_TAC IPOW_LT_0);;
e(SIMP_TAC[REAL_LT_POW2]);;
e(SIMP_TAC[REAL_MUL_POS_LT]);;
e(DISJ1_TAC);;
e(REPEAT STRIP_TAC);;
 e(SIMP_TAC[scale_factor_e]);;
 e(SIMP_TAC[REAL_LT_POW2]);;
 e(SIMP_TAC[scale_factor_f]);;
e(MATCH_MP_TAC REAL_LTE_ADD);;
e(ASM_SIMP_TAC[REAL_LT_01]);;
e(MATCH_MP_TAC REAL_LE_DIV );;
e(REPEAT STRIP_TAC);;
e(SIMP_TAC[REAL_POS]);;
e(SIMP_TAC[REAL_POS]);;
 e(SIMP_TAC[REAL_LE_LT] THEN DISJ1_TAC THEN SIMP_TAC[REAL_LT_POW2]);;
 e(ONCE_ASM_SIMP_TAC[REAL_POLY_CLAUSES]);;
 e(ONCE_ASM_SIMP_TAC[REAL_POLY_CLAUSES]);;
 e(ONCE_ASM_SIMP_TAC[REAL_POLY_CLAUSES]);;
 e(ONCE_ASM_SIMP_TAC[REAL_POLY_CLAUSES]);;
 e(ONCE_ASM_SIMP_TAC[REAL_POLY_CLAUSES]);;
e(ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ;SCALE_REGIME_GT_0]);;
e(SIMP_TAC[maxpos;scale_factor_r;ipow]);;
 e(REPEAT COND_CASES_TAC);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit) (L:bool list)`);;
e(SIMP_TAC[is_valid_posit_length;EQ_SYM_EQ]);;
 e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`num_of_int (value_of_k L) <= ((LENGTH L) - 2)
`ASSUME_TAC);;
 e(SIMP_TAC[GSYM INT_OF_NUM_LE]);;
e(ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;
e(ASM_SIMP_TAC[VAL_K_LE]);;
e(ASM_SIMP_TAC[REAL_NOT_EQ;USEED_GT_0;VAL_K_LE;GSYM REAL_POW_SUB]);;
 e(SUBGOAL_THEN`num_of_int (value_of_k (L:(bool)list)) < LENGTH (L:(bool)list) - 2`ASSUME_TAC);;
e(ASM_SIMP_TAC[GSYM INT_OF_NUM_LT;INT_OF_NUM_OF_INT]);;
e(IMP_REWRITE_TAC[VAL_K_GT_0]);;
e(UNDISCH_TAC`nbits_num (P:posit) = LENGTH (L:(bool)list)`);;
e(ASM_SIMP_TAC[EQ_SYM_EQ;NBITS_GE_2]);;
e(SIMP_TAC[scale_factor_e]);;
e(SIMP_TAC[useed;REAL_POW_POW]);;
e(ASM_CASES_TAC`exp_length (P:posit) (L:(bool)list)< ebits_num (P:posit)`);;
r(1);;
e(SUBGOAL_THEN`&2 pow
 (2 EXP ebits_num (P:posit) *
  (LENGTH (L:(bool)list) - 2 - num_of_int (value_of_k (L:(bool)list)))) = &2 pow
 (SUC(2 EXP ebits_num (P:posit) * (LENGTH (L:(bool)list) - 2 - num_of_int (value_of_k (L:(bool)list))) -
       1))`ASSUME_TAC);;
e(SIMP_TAC[ADD1]);;
e(IMP_REWRITE_TAC[SUB_ADD]);;
e(ONCE_REWRITE_TAC[ARITH_RULE`1 =1 *1`]);;
e(IMP_REWRITE_TAC[LE_MULT2;VAL_K_GT_0;LE_SUC_LT;LT_SUC_LE]);;
e(STRIP_TAC);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW;REAL_LE_POW2]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
 e(SIMP_TAC[real_pow]);;
e(SIMP_TAC[ARITH_RULE`&2 *
 &2 pow
 (2 EXP ebits_num (P:posit) *
  (LENGTH (L:(bool)list) - 2 - num_of_int (value_of_k (L:(bool)list))) -
  1) = 
 &2 pow
 (2 EXP ebits_num (P:posit) *
  (LENGTH (L:(bool)list) - 2 - num_of_int (value_of_k (L:(bool)list))) -
  1) *(&2)`]);;
e(IMP_REWRITE_TAC[REAL_LE_MUL2]);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_LT_POW2;FRAC_LE_2;
is_valid_posit_length;EQ_SYM_EQ;FRAC_GE_0]);;
e(SIMP_TAC[GSYM REAL_LE_LT]);;
e(MATCH_MP_TAC REAL_POW_MONO);;
e(STRIP_TAC);;
e(ARITH_TAC);;
e(SIMP_TAC[GSYM REAL_OF_NUM_MUL]);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW]);;
 e(SIMP_TAC[GSYM REAL_OF_NUM_MUL;GSYM REAL_OF_NUM_POW]);;
e(SUBGOAL_THEN` &2 pow (ebits_num (P:posit) - exp_length (P:posit) (L:(bool)list))
 = (&1)`ASSUME_TAC);;
e(SUBGOAL_THEN`(ebits_num (P:posit) - exp_length (P:posit) (L:(bool)list))
 = (0)`ASSUME_TAC);;
e(ASM_SIMP_TAC[SUB_EQ_0;GSYM NOT_LT]);;
 e(ASM_SIMP_TAC[real_pow]);;
 e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[BV_EXP_LE;REAL_OF_NUM_LE;REAL_MUL_RID]);;
e(MATCH_MP_TAC LE_TRANS);;
e(EXISTS_TAC` (2 EXP ebits_num (P:posit)) - 1`);;
e(ASM_SIMP_TAC[BV_EXP_LE]);;
e(IMP_REWRITE_TAC[EXP2_LE_LEMMA]);;
e(ASM_ARITH_TAC);;
r(1);;
e(IMP_REWRITE_TAC[is_valid_posit_length;FRAC_EQ_1]);;
e(ASM_SIMP_TAC[BV_EXP_LE;REAL_OF_NUM_LE;REAL_MUL_RID]);;
 e(MATCH_MP_TAC REAL_POW_MONO);;
e(STRIP_TAC);;
e(ARITH_TAC);;
e(SIMP_TAC[GSYM REAL_OF_NUM_MUL]);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW]);;
 e(SIMP_TAC[GSYM REAL_OF_NUM_MUL;GSYM REAL_OF_NUM_POW]);;
e(SUBGOAL_THEN `&2 pow
 (ebits_num (P:posit) - (exp_length (P:posit) (L:(bool)list))) = &2 pow
 (ebits_num (P:posit))/(&2) pow ( (exp_length (P:posit) (L:(bool)list)))` ASSUME_TAC);;
 e(MATCH_MP_TAC REAL_POW_SUB);;
 e(STRIP_TAC);;
e(ARITH_TAC);;
e(MATCH_MP_TAC PST_EXP_LENGTH);;
e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[is_valid_posit_length]);;
e(ASM_SIMP_TAC[]);;
 e(SUBGOAL_THEN`(&(BV_n (exp_bits (P:posit) (L:(bool)list)))) 
* ((&2) pow ebits_num (P:posit)) /
 ((&2) pow  (exp_length (P:posit) (L:(bool)list))) =
 ((&(BV_n (exp_bits (P:posit) (L:(bool)list)))) * ((&2) pow ebits_num (P:posit))) /
 ((&2) pow (exp_length (P:posit) (L:(bool)list)))
`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
 e(ASM_SIMP_TAC[is_valid_posit_length]);;
e(ASM_SIMP_TAC[]);;
e(SIMP_TAC[ARITH_RULE`(&(BV_n (exp_bits (P:posit) (L:(bool)list))) *
 &2 pow ebits_num (P:posit)) / &2 pow exp_length (P:posit) (L:(bool)list) = 
(&2 pow ebits_num (P:posit))*(&(BV_n (exp_bits (P:posit) (L:(bool)list)))  / &2 pow exp_length (P:posit) (L:(bool)list))`]);;
 e(IMP_REWRITE_TAC[REAL_LE_LMUL_EQ]);;
 e(SIMP_TAC[REAL_LT_POW2]);;
 e(MATCH_MP_TAC REAL_LE_TRANS);;
e(EXISTS_TAC`(&1)`);;
e(STRIP_TAC);;
r(1);;
 e(SIMP_TAC[REAL_OF_NUM_LE]);;
e(ASM_ARITH_TAC);;
r(1);;
 e(IMP_REWRITE_TAC[GSYM REAL_OF_NUM_LE;LE_LT;VAL_LT_EXP2;REAL_LE_LDIV_EQ;REAL_LT_POW2;REAL_MUL_LID]);;
e(SIMP_TAC[REAL_OF_NUM_LE;LE_LT;REAL_OF_NUM_POW]);;
e(DISJ1_TAC THEN SIMP_TAC[exp_length;VAL_LT_EXP2]);;
e(SUBGOAL_THEN`useed (P:posit) pow (nbits_num (P:posit) - 2) /
 inv (useed (P:posit) pow num_of_int (--value_of_k (L:(bool)list))) = useed (P:posit) pow (nbits_num (P:posit) - 2) *(useed (P:posit) pow num_of_int (--value_of_k (L:(bool)list)))`ASSUME_TAC);;
e(SIMP_TAC[real_div;REAL_POLY_CLAUSES]);;
e(SIMP_TAC[REAL_INV_INV]);;
 e(ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(SIMP_TAC[GSYM REAL_POW_ADD]);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit) (L:(bool)list)`);;
e(REWRITE_TAC[is_valid_posit_length]);;
e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e(SIMP_TAC[]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`0<
(LENGTH (L:(bool)list) - 2 + num_of_int (--value_of_k (L:(bool)list)))`ASSUME_TAC);;
e(ONCE_REWRITE_TAC[ARITH_RULE`0 =0+0`]);;
e(IMP_REWRITE_TAC[LET_ADD2]);;
e(STRIP_TAC);;
r(1);;
 e(IMP_REWRITE_TAC[GSYM INT_OF_NUM_LT;NUM_OF_INT_OF_NUM;INT_OF_NUM_OF_INT]);;
e(ASM_ARITH_TAC);;
r(1);;
e(UNDISCH_TAC`nbits_num (P:posit) = LENGTH (L:bool list)`);;
e(IMP_REWRITE_TAC[NBITS_GE_2;EQ_SYM_EQ;SUB_ADD;LE_0]);;
e(SIMP_TAC[scale_factor_e]);;
e(ASM_CASES_TAC`exp_length (P:posit) (L:(bool)list)< ebits_num (P:posit)`);;
e(IMP_REWRITE_TAC[is_valid_posit_length;FRAC_EQ_1]);;
e(SIMP_TAC[useed;REAL_POW_POW]);;
e(IMP_REWRITE_TAC[REAL_POW_MONO;REAL_MUL_RID]);;
e(STRIP_TAC);;
e(ARITH_TAC);;
r(1);;
 e(SUBGOAL_THEN` &2 pow (ebits_num (P:posit) - exp_length (P:posit) (L:(bool)list))
 = (&1)`ASSUME_TAC);;
e(SUBGOAL_THEN`(ebits_num (P:posit) - exp_length (P:posit) (L:(bool)list))
 = (0)`ASSUME_TAC);;
e(ASM_SIMP_TAC[SUB_EQ_0;GSYM NOT_LT]);;
 e(ASM_SIMP_TAC[real_pow]);;
 e(ASM_SIMP_TAC[]);;
e(SIMP_TAC[useed;REAL_POW_POW]);;
e(SUBGOAL_THEN`&2 pow
 (2 EXP ebits_num (P:posit) *
  (LENGTH (L:(bool)list) - 2 + num_of_int (--value_of_k (L:(bool)list)))) = 
&2 pow (SUC
      ((2 EXP ebits_num (P:posit) *
       (LENGTH (L:(bool)list) - 2 + num_of_int (--value_of_k (L:(bool)list)))) -
       1))`ASSUME_TAC);;
e(SIMP_TAC[ADD1]);;
e(IMP_REWRITE_TAC[SUB_ADD]);;
e(ONCE_REWRITE_TAC[ARITH_RULE`1 =1 *1`]);;
e(IMP_REWRITE_TAC[LE_MULT2;VAL_K_GT_0;LE_SUC_LT;LT_SUC_LE]);;
e(STRIP_TAC);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW;REAL_LE_POW2]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(SIMP_TAC[real_pow]);;
e(ONCE_REWRITE_TAC[ARITH_RULE`&2 * &2 pow
 (2 EXP ebits_num (P:posit) * (LENGTH (L:bool list) - 2 + num_of_int (--value_of_k (L:bool list))) - 1)
 =  (&2 pow
 (2 EXP ebits_num (P:posit) * (LENGTH (L:bool list) - 2 + num_of_int (--value_of_k (L:bool list))) - 1))*(&2)`]);;
e(IMP_REWRITE_TAC[REAL_LE_MUL2]);;
e(REPEAT STRIP_TAC);;
e(ASM_SIMP_TAC[REAL_LT_POW2;REAL_LE_LT]);;
r(1);;
 e(ASM_SIMP_TAC[is_valid_posit_length;FRAC_GE_0;EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[FRAC_LE_2;is_valid_posit_length;EQ_SYM_EQ]);;
r(1);;
e(IMP_REWRITE_TAC[REAL_POW_MONO]);;
e(STRIP_TAC);;
e(ARITH_TAC);;
e(SIMP_TAC[GSYM REAL_OF_NUM_MUL]);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW]);;
 e(SIMP_TAC[GSYM REAL_OF_NUM_MUL;GSYM REAL_OF_NUM_POW]);;
e(ASM_SIMP_TAC[BV_EXP_LE;REAL_OF_NUM_LE;REAL_MUL_RID]);;
e(MATCH_MP_TAC LE_TRANS);;
e(EXISTS_TAC` 2 EXP ebits_num (P:posit) - 1`);;
e(STRIP_TAC);;
 e(ASM_SIMP_TAC[BV_EXP_LE]);;
e(IMP_REWRITE_TAC[EXP2_LE_LEMMA]);;
 e(ASM_ARITH_TAC);; 
e(SIMP_TAC[GSYM REAL_OF_NUM_MUL]);;
e(SIMP_TAC[GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_POW]);;
 e(SIMP_TAC[GSYM REAL_OF_NUM_MUL;GSYM REAL_OF_NUM_POW]);;
 e(SUBGOAL_THEN `&2 pow
 (ebits_num (P:posit) - (exp_length (P:posit) (L:(bool)list))) = &2 pow
 (ebits_num (P:posit))/(&2) pow ( (exp_length (P:posit) (L:(bool)list)))` ASSUME_TAC);;
 e(MATCH_MP_TAC REAL_POW_SUB);;
 e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(ONCE_REWRITE_TAC[ARITH_RULE`m*n/p = n*(m/p)`]);;
e(IMP_REWRITE_TAC[REAL_LE_LMUL_EQ]);;
e(SIMP_TAC[REAL_LT_POW2]);;
e(MATCH_MP_TAC REAL_LE_TRANS);;
e(EXISTS_TAC`(&1)`);;
e(STRIP_TAC);;
e(IMP_REWRITE_TAC[GSYM REAL_OF_NUM_LE;LE_LT;VAL_LT_EXP2;REAL_LE_LDIV_EQ;REAL_LT_POW2;REAL_MUL_LID]);;
e(SIMP_TAC[REAL_OF_NUM_LE;LE_LT;REAL_OF_NUM_POW]);;
e(DISJ1_TAC);;
e(SIMP_TAC[exp_length;VAL_LT_EXP2]);;
e(SIMP_TAC[REAL_OF_NUM_LE]);;
 e(ASM_ARITH_TAC);;
let MAX_VAL = top_thm();;

	 
g`!L P x. (fraction_residue_set1 x P= (&0)) /\
 (x>(&0)) /\ 
~(exponential_round_check1 x P) /\
 (is_valid_posit (dest_posit P)) /\
 (is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P)) /\
(regime_length (APPEND [F]
    (APPEND (regime_bits x P)
    (APPEND (exp_list x P) (set_fraction_list x P)))) = LENGTH (regime_bits x P))  ==> 
(scale_factor_e P (real_to_posit_check3 x P) = (&2) pow (BV_n (exp_list x P)))`;;
e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[scale_factor_e]);;
e(IMP_REWRITE_TAC[REAL_POW_EQ2;LIST_EQ]);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(SIMP_TAC[exp_bits]);;
e(REPEAT COND_CASES_TAC);;
r(1);;
r(1);;
e(SUBGOAL_THEN`ebits_num P = 0`ASSUME_TAC);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[exp_list]);;
e(ASM_SIMP_TAC[num_BV_f;REVERSE;num_BV]);;
e(ASM_SIMP_TAC[BV_n]);;
e(ARITH_TAC);;
r(1);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3]);;
e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE;exponential_round_check1]);;
e(STRIP_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[GSYM APPEND_ASSOC]);;
e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[GSYM ADD1;pick_elements;TL;L_ADD1;APPEND]);;
e(SUBGOAL_THEN`(SUC
 ((LENGTH (regime_bits x P) + ebits_num P) - SUC (LENGTH (regime_bits x P)))) = ebits_num P`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN`ebits_num P = LENGTH (exp_list x P)`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f;EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[THRD_LIST_APPEND]);;
e(STRIP_TAC);;
r(1);;
e(ASM_ARITH_TAC);;
e(ONCE_ASM_REWRITE_TAC[ARITH_RULE
`BV_n (exp_list (x:real) (P:posit)) = BV_n (exp_list (x:real) (P:posit)) *1`]);;
e(ONCE_ASM_REWRITE_TAC[ARITH_RULE`(m*1)*n = m*n`]);;
 e(ASM_SIMP_TAC[MULT_CLAUSES;EQ_MULT_LCANCEL]);;
e(DISJ2_TAC);;
e(ASM_SIMP_TAC[EXP_EQ_1]);;
e(ASM_SIMP_TAC[SUB_EQ_0]);;
 e(IMP_REWRITE_TAC[EXP_LENGTH_EQ2]);;
e(SIMP_TAC[LE_REFL]);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3]);;
e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE;exponential_round_check1]);;
e(STRIP_TAC);;
e(ONCE_ASM_SIMP_TAC[GSYM NOT_LT;EQ_SYM_EQ;GSYM APPEND_SING;APPEND_ASSOC]);;
e(ONCE_ASM_SIMP_TAC[GSYM NOT_LT;EQ_SYM_EQ;GSYM APPEND_SING;APPEND_ASSOC]);;
e(ONCE_ASM_SIMP_TAC[GSYM NOT_LT;EQ_SYM_EQ;GSYM APPEND_SING;APPEND_ASSOC]);;
e(ONCE_ASM_SIMP_TAC[GSYM NOT_LT;EQ_SYM_EQ;GSYM APPEND_SING;APPEND_ASSOC]);;
e(ASM_ARITH_TAC);;
let EXP_CONV = top_thm();;



g`!(L: bool list) P x. (fraction_residue_set1 x P= (&0)) /\
 (x>(&0)) /\ 
~(exponential_round_check1 x P) /\
 (is_valid_posit (dest_posit P)) /\
 (is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P)) /\
(regime_length (APPEND [F]
    (APPEND (regime_bits x P)
    (APPEND (exp_list x P) (set_fraction_list x P)))) = LENGTH (regime_bits x P))  ==> 
(scale_factor_f P (real_to_posit_check3 x P) = (&1) + 
((&(BV_n (set_fraction_list x P)))/(&2 pow (LENGTH (set_fraction_list x P)))))`;;
e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[scale_factor_f;REAL_EQ_ADD_LCANCEL]);;
e(IMP_REWRITE_TAC[RAT_LEMMA5;LIST_EQ]);;
e(SIMP_TAC[REAL_LT_POW2]);;
e(ASM_SIMP_TAC[ real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(SIMP_TAC[fraction_bits]);;
e(REPEAT COND_CASES_TAC);;
r(1);;
e(SIMP_TAC[BV_n;REAL_MUL_LZERO]);;
e(SIMP_TAC[REAL_ENTIRE;EQ_SYM_EQ]);;
e(DISJ1_TAC);;
e(SUBGOAL_THEN`(set_fraction_list (x:real) (P:posit)) = []`ASSUME_TAC);;
e(ASM_SIMP_TAC[set_fraction_list]);;
e(SUBGOAL_THEN` (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  ebits_num (P:posit) -
  1) =0`ASSUME_TAC);;
 e(SUBGOAL_THEN`exp_length (P:posit)
 (APPEND [F]
 (APPEND (regime_bits (x:real) (P:posit))
 (APPEND (exp_list (x:real) (P:posit))
 (set_fraction_list (x:real) (P:posit))))) <= ebits_num P`ASSUME_TAC);;
e(IMP_REWRITE_TAC[PST_EXP_LENGTH]);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[fraction_list]);;
e(ASM_SIMP_TAC[BV_n]);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(ASM_SIMP_TAC[FRAC_LENGTH;LENGTH_FRAC]);;
 e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN` exp_length P
   (APPEND [F]
   (APPEND (regime_bits x P)
   (APPEND (exp_list x P)
   (set_fraction_list x P )))) = ebits_num P`ASSUME_TAC);;
 e(IMP_REWRITE_TAC[EXP_LENGTH_EQ2]);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(ASM_SIMP_TAC[exponential_round_check1]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[set_fraction_list;LENGTH_FRAC]);;
e(SIMP_TAC[ARITH_RULE`(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit)) + ebits_num (P:posit) + 1)) = 
(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit))) - ebits_num (P:posit) - 1)`]);;
e(ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL]);;
e(DISJ1_TAC);;
e(IMP_REWRITE_TAC[LIST_EQ;REAL_OF_NUM_EQ]);;
e(ASM_REWRITE_TAC[pick_elements;GSYM ADD1]);;
e(ASM_SIMP_TAC[ARITH_RULE`(LENGTH (regime_bits (x:real) (P:posit)) + SUC (ebits_num (P:posit)))
= SUC (LENGTH (regime_bits (x:real) (P:posit)) + (ebits_num (P:posit)))`]);;
e(IMP_REWRITE_TAC[L_ADD1;TL;APPEND]);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (APPEND [F]
      (APPEND (regime_bits (x:real) (P:posit))
      (APPEND (exp_list (x:real) (P:posit))
      (set_fraction_list (x:real) (P:posit)))))`);;
e(ASM_SIMP_TAC[is_valid_posit_length;LENGTH_APPEND;LENGTH;ADD1]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  1 -((LENGTH (regime_bits (x:real) (P:posit)) + ebits_num (P:posit)) + 1) +
  1)= (nbits_num (P:posit) - LENGTH (regime_bits (x:real) (P:posit)) -
 ebits_num (P:posit) - 1)`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SUBGOAL_THEN`(ebits_num (P:posit)) = LENGTH (exp_list (x:real) (P:posit))`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1) = LENGTH (fraction_list
 ((x:real) /
  (scale_factor_r (P:posit) (CONS (sign_real x) (regime_bits x P)) *
   &2 pow BV_n (exp_list (x:real) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1))`ASSUME_TAC);;
e(ASM_SIMP_TAC[LENGTH_FRAC;EQ_SYM_EQ]);;
e(SUBGOAL_THEN`0 < LENGTH (fraction_list
 ((x:real) /
  (scale_factor_r (P:posit) (CONS (sign_real x) (regime_bits x P)) *
   &2 pow BV_n (exp_list (x:real) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
 e(ASM_MESON_TAC[FRTH_LIST_APPEND]);;
let FRAC_CONV = top_thm();;

g`! n x. (fraction_residue1 x n = &0) ==> 
(x = (&(BV_n (fraction_list x n))) /
 ((&2) pow (LENGTH (fraction_list x n))))`;;
e(INDUCT_TAC);;
e(SIMP_TAC[fraction_residue1;fraction_list;BV_n]);;
e(ARITH_TAC);;
e(SIMP_TAC[fraction_residue1;fraction_list;BV_n]);;
e(STRIP_TAC);;
e(COND_CASES_TAC);;
e(SIMP_TAC[]);;
r(1);;
e(SIMP_TAC[]);;
e(SIMP_TAC[BV_n;BV;MULT_CLAUSES;ADD_CLAUSES]);;
e(FIRST_X_ASSUM(MP_TAC o SPEC `((x:real) * &2)`));;
e(ASM_SIMP_TAC[EQ_SYM_EQ;LENGTH;pow]);;
e(REPEAT STRIP_TAC);;
 e(IMP_REWRITE_TAC[REAL_EQ_RDIV_EQ;REAL]);;
e(IMP_REWRITE_TAC[REAL_LT_POW2;REAL_LT_MUL]);;
e(STRIP_TAC);;
r(1);;
 e(ARITH_TAC);;
r(1);;
e(SIMP_TAC[ARITH_RULE`(x:real) * &2 * &2 pow LENGTH (fraction_list ((x:real) * &2) (n:num))=
((x:real) * &2) * &2 pow LENGTH (fraction_list ((x:real) * &2) (n:num))`]);;
e(IMP_REWRITE_TAC[GSYM REAL_EQ_RDIV_EQ;REAL_LT_POW2]);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[BV_n;BV;MULT_CLAUSES]);;
e(SIMP_TAC[BV_n;BV;MULT_CLAUSES]);;
e(FIRST_X_ASSUM(MP_TAC o SPEC `(&2 * (x:real) - &1)`));;
e(ASM_SIMP_TAC[EQ_SYM_EQ;LENGTH;pow]);;
e(REPEAT STRIP_TAC);;
 e(IMP_REWRITE_TAC[REAL_EQ_RDIV_EQ;REAL]);;
e(IMP_REWRITE_TAC[REAL_LT_POW2;REAL_LT_MUL]);;
e(STRIP_TAC);;
r(1);;
 e(ARITH_TAC);;
e(SIMP_TAC[ARITH_RULE`(x:real) * &2 * &2 pow LENGTH (fraction_list (&2 * (x:real) - &1) (n:num))=
((x:real) * &2) * &2 pow LENGTH (fraction_list (&2 * (x:real) - &1) (n:num))`]);;
e(SIMP_TAC[GSYM REAL_OF_NUM_ADD;GSYM REAL_OF_NUM_POW;REAL_ADD_SYM]);;
e(ASM_SIMP_TAC[GSYM REAL_EQ_SUB_RADD]);;
e(SIMP_TAC[ARITH_RULE`((x:real) * &2) * &2 pow LENGTH (fraction_list (&2 * (x:real) - &1) (n:num)) -
 &2 pow LENGTH (fraction_list (&2 * (x:real) - &1) (n:num)) = 
(((x:real) * &2)- (&1)) * &2 pow LENGTH (fraction_list (&2 * (x:real) - &1) (n:num))`]);;
e(IMP_REWRITE_TAC[GSYM REAL_EQ_RDIV_EQ;REAL_LT_POW2]);;
e(ASM_ARITH_TAC);;
let ZERO_RESIDUE_VAL = top_thm();;

g`!L P x. (fraction_residue_set1 x P= (&0))/\(x>(&0))/\ 
~(exponential_round_check1 x P) /\
 (is_valid_posit (dest_posit P)) /\ 
(is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P) ) /\
(regime_length (APPEND [F]
    (APPEND (regime_bits x P)
    (APPEND (exp_list x P) (set_fraction_list x P)))) = LENGTH (regime_bits x P)) /\
(value_of_k (real_to_posit_check3 (x:real) (P:posit)) = 
value_of_k  (APPEND [sign_real x] (regime_bits x P)))
==> add_zero_real P (real_to_posit_check3 x P) = x `;;
e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[add_zero_real]);;
e(ASM_SIMP_TAC[posit_to_signed_real]);;
e(SUBGOAL_THEN`~(sign_bit (real_to_posit_check3 x P))`ASSUME_TAC);;
 e(ASM_SIMP_TAC[SIGN_ENCODE_DECODE]);;
e(ASM_SIMP_TAC[]);;
 e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1]);;
e(ASM_SIMP_TAC[sign_bit;HD;APPEND]);;
e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[EXP_CONV;FRAC_CONV]);;
e(ASM_SIMP_TAC[ARITH_RULE`scale_factor_r (P:posit) (real_to_posit_check3 (x:real) (P:posit)) *
 &2 pow BV_n (exp_list (x:real) (P:posit)) *
 (&1 +
  &(BV_n (set_fraction_list (x:real) (P:posit))) /
  &2 pow LENGTH (set_fraction_list (x:real) (P:posit))) = (&1 +
  &(BV_n (set_fraction_list (x:real) (P:posit))) /
  &2 pow LENGTH (set_fraction_list (x:real) (P:posit))) * 
(scale_factor_r (P:posit) (real_to_posit_check3 (x:real) (P:posit))) * 
&2 pow BV_n (exp_list (x:real) (P:posit)) 
 `]);;
e(IMP_REWRITE_TAC[GSYM REAL_EQ_RDIV_EQ;REAL_LT_POW2]);;
e(IMP_REWRITE_TAC[SCALE_REGIME_GT_0;REAL_LT_POW2;REAL_LT_MUL]);;
e(ASM_SIMP_TAC[REAL_ADD_SYM]);;
e(ASM_SIMP_TAC[GSYM REAL_EQ_SUB_LADD]);;
e(UNDISCH_TAC`fraction_residue_set1 (x:real) (P:posit) = &0`);;
e(ASM_SIMP_TAC[fraction_residue_set1]);;
e(SUBGOAL_THEN` LENGTH (exp_list (x:real) (P:posit))= (ebits_num (P:posit)) `ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`&(BV_n
  (fraction_list
   ((x:real) /
    (scale_factor_r (P:posit) (APPEND [sign_real x] (regime_bits x P)) *
     &2 pow BV_n (exp_list (x:real) (P:posit))) -
    &1)
  (nbits_num (P:posit) -
   LENGTH (regime_bits (x:real) (P:posit)) -
   ebits_num (P:posit) -
   1))) /
 &2 pow
 LENGTH
 (fraction_list
  ((x:real) /
   (scale_factor_r (P:posit) (APPEND [sign_real x] (regime_bits x P)) *
    &2 pow BV_n (exp_list (x:real) (P:posit))) -
   &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  ebits_num (P:posit) -
  1)) = ((x:real) /
   (scale_factor_r (P:posit) (APPEND [sign_real x] (regime_bits x P)) *
    &2 pow BV_n (exp_list (x:real) (P:posit))) -
   &1)`ASSUME_TAC);;
 e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[ZERO_RESIDUE_VAL]);;
e(ASM_SIMP_TAC[set_fraction_list]);;
e(ASM_SIMP_TAC[scale_factor_r]);;
let  EXACT_POSIT_CONV_ASSUMS =top_thm();;

g`!(L:bool list) P x. (fraction_residue_set1 (abs x) P= (&0))/\(~(x= (&0)))/\ 
~(exponential_round_check1 (abs x) P) /\
 (is_valid_posit (dest_posit P)) /\ 
(is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P) ) /\
(!A.two_complement (two_complement A ) = A )/\
(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P)) /\
(value_of_k ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = 
value_of_k  (APPEND [sign_real (abs x)] (regime_bits (abs x) P)))
==> add_zero_real P (real_to_posit_check3 x P) = x `;;
e(REPEAT STRIP_TAC);;
e(ASM_CASES_TAC`x > &0`);;
 e(MATCH_MP_TAC EXACT_POSIT_CONV_ASSUMS);;
 e(ASM_SIMP_TAC[]);;
e(UNDISCH_TAC`~exponential_round_check1 (abs x) P`);;
 e(ASM_SIMP_TAC[real_abs;REAL_LE_LT;GSYM real_gt]);;
e(UNDISCH_TAC`fraction_residue_set1 (abs x) P = &0`);;
 e(ASM_SIMP_TAC[real_abs;REAL_LE_LT;GSYM real_gt]);;
e(REPEAT STRIP_TAC);;
e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(SUBGOAL_THEN`~(x < (&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[APPEND;real_abs;REAL_LE_LT;GSYM real_gt]);;
e(ASM_SIMP_TAC[real_to_posit_check3;fraction_rounding1]);;
e(UNDISCH_TAC`value_of_k
      (CONS (sign_real (x:real))
      (APPEND (regime_bits (abs (x:real)) (P:posit))
      (APPEND (exp_list (abs (x:real)) (P:posit))
      (set_fraction_list (abs (x:real)) (P:posit))))) =
      value_of_k
      (APPEND [sign_real (abs (x:real))]
      (regime_bits (abs (x:real)) (P:posit)))`);;
e(ASM_SIMP_TAC[sign_real;APPEND]);;
 e(ASM_SIMP_TAC[real_abs;REAL_LE_LT;GSYM real_gt]);;
e(SUBGOAL_THEN`~(x < (&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
 e(ASM_SIMP_TAC[real_gt]);;
e(ASM_SIMP_TAC[add_zero_real;sign_bit;posit_to_signed_real;NOT_CONS_NIL;HD;HD_APPEND;TL;SIGN_ENCODE_DECODE_NEG;REAL_NOT_LT;real_gt]);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1]);;
e(ASM_SIMP_TAC[APPEND;TL;HD]);;
e(SUBGOAL_THEN`scale_factor_e P
    (CONS T
    (APPEND (regime_bits (abs x) P)
    (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) = (&2 pow (BV_n(exp_list (abs x) P) ))`ASSUME_TAC);;

e(SIMP_TAC[scale_factor_e]);;
e(IMP_REWRITE_TAC[REAL_POW_EQ2;LIST_EQ]);;
e(SUBGOAL_THEN`2 EXP
  (ebits_num P -
   exp_length P
   (CONS T
   (APPEND (regime_bits (abs x) P)
   (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = 1`ASSUME_TAC);;
e(IMP_REWRITE_TAC [EXP_EQ_1]);;
e(DISJ2_TAC);;
 e(IMP_REWRITE_TAC [SUB_EQ_0]);;
e(UNDISCH_TAC`~exponential_round_check1 (abs x) P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
 e(IMP_REWRITE_TAC [EXP_LENGTH_EQ2]);;
 e(ASM_SIMP_TAC[LE_REFL;GSYM NOT_LT;LT_REFL]);;
 e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
 e(ASM_SIMP_TAC[REAL_LE_LT]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
 e(ASM_SIMP_TAC[MULT_CLAUSES]);;



e(SIMP_TAC[exp_bits]);;
e(COND_CASES_TAC);;
r(1);;
e(SUBGOAL_THEN`ebits_num P = 0`ASSUME_TAC);;
e(UNDISCH_TAC`~exponential_round_check1 (abs x) P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
 e(ASM_ARITH_TAC);;
e(SIMP_TAC[exp_list]);;
e(ASM_SIMP_TAC[num_BV_f;REVERSE;num_BV]);;
e(SIMP_TAC[MULT_CLAUSES;BV_n]);;
r(1);;

 e(SUBGOAL_THEN`regime_length
     (CONS T
     (APPEND (regime_bits (abs x) P)
     (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) +
     1 +
     ebits_num P <=
     LENGTH
     (CONS T
     (APPEND (regime_bits (abs x) P)
     (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))`ASSUME_TAC);;
e(UNDISCH_TAC`~exponential_round_check1 (abs x) P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
 e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[]);;

e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
e(ASM_SIMP_TAC[GSYM ADD1;pick_elements;TL;L_ADD1]);;
e(SUBGOAL_THEN`(SUC
 ((LENGTH (regime_bits (abs x) P) + ebits_num P) -
  SUC (LENGTH (regime_bits (abs x) P))))= ebits_num P `ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SUBGOAL_THEN`ebits_num P = LENGTH (exp_list( abs x) P)`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f;EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[THRD_LIST_APPEND]);;
 e(ASM_ARITH_TAC);;
 e(ASM_SIMP_TAC[]);;
 e(ASM_SIMP_TAC[]);;




e(SUBGOAL_THEN`(scale_factor_f P (CONS T
    (APPEND (regime_bits (abs x) P)
    (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) = (&1) + 
((&(BV_n (set_fraction_list (abs x) P)))/(&2 pow (LENGTH (set_fraction_list (abs x) P)))))`
ASSUME_TAC);;
e(SIMP_TAC[scale_factor_f;REAL_EQ_ADD_LCANCEL]);;
e(IMP_REWRITE_TAC[RAT_LEMMA5;LIST_EQ]);;
e(SIMP_TAC[REAL_LT_POW2]);;
e(SIMP_TAC[fraction_bits]);;
e(REPEAT COND_CASES_TAC);;
r(1);;
e(SIMP_TAC[BV_n;REAL_MUL_LZERO]);;
e(SIMP_TAC[REAL_ENTIRE;EQ_SYM_EQ]);;
e(DISJ1_TAC);;
e(SUBGOAL_THEN`(set_fraction_list (abs (x:real)) (P:posit)) = []`ASSUME_TAC);;
e(ASM_SIMP_TAC[set_fraction_list]);;
e(SUBGOAL_THEN` (nbits_num (P:posit) -
  LENGTH (regime_bits (abs (x:real)) (P:posit)) -
  ebits_num (P:posit) -
  1) =0`ASSUME_TAC);;
 e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
 e(SUBGOAL_THEN`exp_length (P:posit)
 (CONS T
 (APPEND (regime_bits (abs (x:real)) (P:posit))
 (APPEND (exp_list (abs (x:real)) (P:posit))
 (set_fraction_list (abs (x:real)) (P:posit))))) <= ebits_num P`ASSUME_TAC);;
e(IMP_REWRITE_TAC[PST_EXP_LENGTH]);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[FRAC_LENGTH;LENGTH_FRAC;fraction_list]);;
e(ASM_SIMP_TAC[BV_n]);;
r(1);;
e(SUBGOAL_THEN`fraction_length P
 (CONS T
 (APPEND (regime_bits (abs x) P)
 (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) =  
nbits_num P - (regime_length (CONS T
 (APPEND (regime_bits (abs x) P)
 (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) + exp_length P (CONS T
 (APPEND (regime_bits (abs x) P)
 (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) + 1)` ASSUME_TAC);;
 e(IMP_REWRITE_TAC[FRAC_LENGTH]);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN` exp_length P
 (CONS T
   (APPEND (regime_bits (abs x) P)
   (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) = ebits_num P`ASSUME_TAC);;
 e(IMP_REWRITE_TAC[EXP_LENGTH_EQ2]);;
e(UNDISCH_TAC`~exponential_round_check1 (abs x) P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;

 e(UNDISCH_TAC`(regime_length ((CONS (sign_real x)
        (APPEND (regime_bits (abs x) P)
        (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) = LENGTH (regime_bits (abs x) P))`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(ASM_SIMP_TAC[]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(UNDISCH_TAC`regime_length
      (CONS (sign_real x)
      (APPEND (regime_bits (abs x) P)
      (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) =
      LENGTH (regime_bits (abs x) P)`);;
e(ASM_SIMP_TAC[sign_real]);;
e(UNDISCH_TAC`~(x > &0)`);;
e(ASM_SIMP_TAC[REAL_LE_LT;REAL_NOT_LT;real_gt]);;
e(REPEAT STRIP_TAC);;
e(ASM_SIMP_TAC[set_fraction_list;LENGTH_FRAC]);;
e(SIMP_TAC[ARITH_RULE`(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit)) + ebits_num (P:posit) + 1)) = 
(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit))) - ebits_num (P:posit) - 1)`]);;
e(ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL]);;
e(DISJ1_TAC);;
e(IMP_REWRITE_TAC[LIST_EQ;REAL_OF_NUM_EQ]);;
e(ASM_REWRITE_TAC[pick_elements;GSYM ADD1]);;
e(ASM_SIMP_TAC[ARITH_RULE`(LENGTH (regime_bits (abs (x:real)) (P:posit)) + SUC (ebits_num (P:posit)))
= SUC (LENGTH (regime_bits (abs (x:real)) (P:posit)) + (ebits_num (P:posit)))`]);;
e(IMP_REWRITE_TAC[L_ADD1;TL;APPEND]);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(ASM_SIMP_TAC[]);;
e(STRIP_TAC);;
e(ASM_SIMP_TAC[ADD1]);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  1 -((LENGTH (regime_bits (abs (x:real)) (P:posit)) + ebits_num (P:posit)) + 1) +
  1)= (nbits_num (P:posit) - LENGTH (regime_bits (abs (x:real)) (P:posit)) -
 ebits_num (P:posit) - 1)`ASSUME_TAC);;
e(ASM_ARITH_TAC);;

e(SUBGOAL_THEN`(ebits_num (P:posit)) = LENGTH (exp_list (abs (x:real)) (P:posit))`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  LENGTH (regime_bits (abs (x:real)) (P:posit)) -
  LENGTH (exp_list (abs (x:real)) (P:posit)) -
  1) = LENGTH (fraction_list
 ((abs (x:real)) /
  (scale_factor_r (P:posit) (CONS (sign_real (abs (x:real))) (regime_bits (abs (x:real)) P)) *
   &2 pow BV_n (exp_list (abs (x:real)) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (abs (x:real)) (P:posit)) -
  LENGTH (exp_list (abs (x:real)) (P:posit)) -
  1))` ASSUME_TAC);;
e(ASM_SIMP_TAC[LENGTH_FRAC;EQ_SYM_EQ]);;
e(SUBGOAL_THEN`0 < LENGTH (fraction_list
 ((x:real) /
  (scale_factor_r (P:posit) (CONS (sign_real (abs (x:real))) (regime_bits (abs (x:real)) P)) *
   &2 pow BV_n (exp_list (abs (x:real)) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (abs (x:real))(P:posit)) -
  LENGTH (exp_list (abs (x:real)) (P:posit)) -
  1))`ASSUME_TAC);;
e(ASM_SIMP_TAC[LENGTH_FRAC]);;
e(ASM_ARITH_TAC);;
e(UNDISCH_TAC`nbits_num P -
      LENGTH (regime_bits (abs x) P) -
      LENGTH (exp_list (abs x) P) -
      1 =
      LENGTH
      (fraction_list
       (abs x /
        (scale_factor_r P (CONS (sign_real (abs x)) (regime_bits (abs x) P)) *
         &2 pow BV_n (exp_list (abs x) P)) -
        &1)
      (nbits_num P -
       LENGTH (regime_bits (abs x) P) -
       LENGTH (exp_list (abs x) P) -
       1))`);;
e(ASM_MESON_TAC[FRTH_LIST_APPEND;LENGTH_FRAC]);;
 e(ASM_SIMP_TAC[]);;
e(SIMP_TAC[ARITH_RULE`(--(scale_factor_r P
   (CONS T
   (APPEND (regime_bits (abs x) P)
   (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) *
 &2 pow BV_n (exp_list (abs x) P) *
 (&1 +
  &(BV_n (set_fraction_list (abs x) P)) /
  &2 pow LENGTH (set_fraction_list (abs x) P))) =
 x) = (scale_factor_r P
   (CONS T
   (APPEND (regime_bits (abs x) P)
   (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) *
 &2 pow BV_n (exp_list (abs x) P) *
 (&1 +
  &(BV_n (set_fraction_list (abs x) P)) /
  &2 pow LENGTH (set_fraction_list (abs x) P)) =
 --x)`]);;
e(ASM_SIMP_TAC[ARITH_RULE`scale_factor_r (P:posit) (CONS T
 (APPEND (regime_bits (abs x) P)
 (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P)))) *
 &2 pow BV_n (exp_list (abs (x:real)) (P:posit)) *
 (&1 +
  &(BV_n (set_fraction_list (abs (x:real)) (P:posit))) /
  &2 pow LENGTH (set_fraction_list (abs (x:real)) (P:posit))) = (&1 +
  &(BV_n (set_fraction_list (abs (x:real)) (P:posit))) /
  &2 pow LENGTH (set_fraction_list (abs (x:real)) (P:posit))) * 
(scale_factor_r (P:posit) (CONS T
 (APPEND (regime_bits (abs x) P)
 (APPEND (exp_list (abs x) P) (set_fraction_list (abs x) P))))) * 
&2 pow BV_n (exp_list (abs x) (P:posit)) 
 `]);;
e(IMP_REWRITE_TAC[GSYM REAL_EQ_RDIV_EQ;REAL_LT_POW2]);;
e(IMP_REWRITE_TAC[SCALE_REGIME_GT_0;REAL_LT_POW2;REAL_LT_MUL]);;
e(ASM_SIMP_TAC[REAL_ADD_SYM]);;
e(ASM_SIMP_TAC[GSYM REAL_EQ_SUB_LADD]);;
e(UNDISCH_TAC`is_valid_posit_length P (real_to_posit_check3 x P)`);;
 e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3;fraction_rounding1;
exponential_round_check1;GSYM REAL_NOT_LE;real_gt]);;
e(ASM_SIMP_TAC[REAL_LE_LT;DE_MORGAN_THM]);;
e(ASM_SIMP_TAC[LENGTH_TWO_COMP;LENGTH_APPEND;LENGTH;ADD_CLAUSES]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN` LENGTH (exp_list (abs (x:real)) (P:posit))= (ebits_num (P:posit)) `ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(ASM_SIMP_TAC[set_fraction_list]);;
e(SUBGOAL_THEN` LENGTH (exp_list (abs (x:real)) (P:posit))= (ebits_num (P:posit)) `ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`&(BV_n
  (fraction_list
   ((abs x) /
    (scale_factor_r (P:posit) (APPEND [sign_real (abs x)] (regime_bits (abs x) P)) *
     &2 pow BV_n (exp_list (abs x) (P:posit))) -
    &1)
  (nbits_num (P:posit) -
   LENGTH (regime_bits (abs x) (P:posit)) -
   ebits_num (P:posit) -
   1))) /
 &2 pow
 LENGTH
 (fraction_list
  ((abs x) /
   (scale_factor_r (P:posit) (APPEND [sign_real (abs x)] (regime_bits (abs x) P)) *
    &2 pow BV_n (exp_list (abs x) (P:posit))) -
   &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (abs x) (P:posit)) -
  ebits_num (P:posit) -
  1)) = ((abs x) /
   (scale_factor_r (P:posit) (APPEND [sign_real (abs x)] (regime_bits (abs x) P)) *
    &2 pow BV_n (exp_list (abs x) (P:posit))) -
   &1)`ASSUME_TAC);;
 e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[ZERO_RESIDUE_VAL]);;
e(UNDISCH_TAC`fraction_residue_set1 (abs x) P = &0`);;
e(ASM_SIMP_TAC[set_fraction_list;fraction_residue_set1]);;
 e(ASM_SIMP_TAC[real_abs;REAL_LE_LT;GSYM real_gt]);;
e(UNDISCH_TAC`value_of_k
      (CONS (sign_real (x:real))
      (APPEND (regime_bits (abs (x:real)) (P:posit))
      (APPEND (exp_list (abs (x:real)) (P:posit))
      (set_fraction_list (abs (x:real)) (P:posit))))) =
      value_of_k
      (APPEND [sign_real (abs (x:real))]
      (regime_bits (abs (x:real)) (P:posit)))`);;
e(ASM_SIMP_TAC[scale_factor_r;real_abs;GSYM real_gt;REAL_LE_LT;K_SAME;sign_real;scale_factor_r;set_fraction_list]);;
e(ASM_SIMP_TAC[real_gt;REAL_NEG_LT0]);;
e(ASM_SIMP_TAC[GSYM real_gt]);;
e(UNDISCH_TAC`~((x:real) > &0)`);;
e(ASM_SIMP_TAC[real_gt]);;
e(ASM_SIMP_TAC[REAL_NOT_LT;REAL_LE_LT;APPEND;K_SAME;set_fraction_list]);;
let EXACT_POSIT_ALL = top_thm();;

g`!L P x. ~(fraction_residue_set1 x P= (&0)) /\ (fraction_residue_set1 x P < (&1)/(&2)) /\
 (x>(&0)) /\ 
~(exponential_round_check1 x P) /\
 (is_valid_posit (dest_posit P)) /\
 (is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P)) /\
(regime_length (APPEND [F]
    (APPEND (regime_bits x P)
    (APPEND (exp_list x P) (set_fraction_list x P)))) = LENGTH (regime_bits x P))  ==> 
(scale_factor_e P (APPEND [F] (frac_posit_down (x:real) (P:posit))) = (&2) pow (BV_n (exp_list x P)))`;;
e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[scale_factor_e]);;
e(IMP_REWRITE_TAC[REAL_POW_EQ2;LIST_EQ]);;
e(UNDISCH_TAC`fraction_residue_set1 (x:real) (P:posit) < &1 / &2`);;
e(ASM_SIMP_TAC[GSYM REAL_NOT_LE]);;
e(ASM_SIMP_TAC[real_gt;REAL_LE_LT;DE_MORGAN_THM]);;
 e(ASM_SIMP_TAC[frac_posit_down]);;
e(REPEAT STRIP_TAC);;
e(SIMP_TAC[exp_bits]);;
e(REPEAT COND_CASES_TAC);;
r(1);;
r(1);;
e(SUBGOAL_THEN`ebits_num P = 0`ASSUME_TAC);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(ASM_ARITH_TAC);;
 e(ASM_SIMP_TAC[BV_n;exp_list;num_BV_f;REVERSE;num_BV]);;
e(ASM_ARITH_TAC);;
r(1);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1]);;
e(STRIP_TAC);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3]);;
e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE;exponential_round_check1]);;
e(ASM_SIMP_TAC[real_gt;frac_posit_down]);;
e(STRIP_TAC);;
e(ASM_ARITH_TAC);;
e(SUBGOAL_THEN`2 EXP
 (ebits_num (P:posit) -
  exp_length (P:posit) (real_to_posit_check3 (x:real) (P:posit))) = 1 `ASSUME_TAC);;
e(SIMP_TAC[EXP_EQ_1]);;
e(DISJ2_TAC);;
e(ASM_SIMP_TAC[SUB_EQ_0]);;
e(IMP_REWRITE_TAC[EXP_LENGTH_EQ2]);;
e(SIMP_TAC[LE_REFL]);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(SIMP_TAC[exponential_round_check1;NOT_LT]);;
e(REPEAT STRIP_TAC);;
e(ASM_SIMP_TAC[is_valid_posit_length;real_to_posit_check3]);;
e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE;exponential_round_check1]);;
e(ASM_SIMP_TAC[real_gt;frac_posit_down]);;
e(STRIP_TAC);;
e(ASM_ARITH_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(UNDISCH_TAC`2 EXP
      (ebits_num (P:posit) -
       exp_length (P:posit) (real_to_posit_check3 (x:real) (P:posit))) =
      1`);;
e(ASM_SIMP_TAC[real_to_posit_check3]);; 
e(ASM_SIMP_TAC[exponential_round_check1;GSYM NOT_LE;fraction_rounding1]);;
e(ASM_SIMP_TAC[real_gt;frac_posit_down]);;
e(ASM_SIMP_TAC[MULT_CLAUSES]);;
e(IMP_REWRITE_TAC[REAL_POW_EQ2;LIST_EQ]);;
 e(STRIP_TAC);;
e(ASM_SIMP_TAC[GSYM ADD1;pick_elements;TL;L_ADD1;APPEND]);;
e(SUBGOAL_THEN`(SUC
 ((LENGTH (regime_bits x P) + ebits_num P) - SUC (LENGTH (regime_bits x P)))) = ebits_num P`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN`ebits_num P = LENGTH (exp_list x P)`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f;EQ_SYM_EQ]);;
e(IMP_REWRITE_TAC[THRD_LIST_APPEND]);;
 e(ASM_ARITH_TAC);;
let FRAC_DOWN_EXP = top_thm();;


g`!(L: bool list) P x. ~(fraction_residue_set1 x P= (&0)) /\(fraction_residue_set1 x P< ((&1)/(&2))) /\
 (x>(&0)) /\ 
~(exponential_round_check1 x P) /\
 (is_valid_posit (dest_posit P)) /\
 (is_valid_posit_length P (real_to_posit_check3 x P)) /\
~( zero_exception (real_to_posit_check3 x P)) /\
~(checkmax (real_to_posit_check3 x P))/\
~(abs x >= maxpos P \/ abs x <= minpos P) /\
~( inf_exception (real_to_posit_check3 x P)) /\
(regime_length (APPEND [F]
    (APPEND (regime_bits x P)
    (APPEND (exp_list x P) (set_fraction_list x P)))) = LENGTH (regime_bits x P))  ==> 
(scale_factor_f P (APPEND [F] (frac_posit_down (x:real) (P:posit))) = (&1) + 
((&(BV_n (set_fraction_list x P)))/(&2 pow (LENGTH (set_fraction_list x P)))))`;;
e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN`~(x=(&0))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SIMP_TAC[scale_factor_f;REAL_EQ_ADD_LCANCEL]);;
e(IMP_REWRITE_TAC[RAT_LEMMA5;LIST_EQ]);;
e(SIMP_TAC[REAL_LT_POW2]);;
e(SIMP_TAC[frac_posit_down]);;



e(SIMP_TAC[fraction_bits]);;
e(REPEAT COND_CASES_TAC);;
r(1);;
e(SIMP_TAC[BV_n;REAL_MUL_LZERO]);;
e(SIMP_TAC[REAL_ENTIRE;EQ_SYM_EQ]);;
e(DISJ1_TAC);;
e(SUBGOAL_THEN`(set_fraction_list (x:real) (P:posit)) = []`ASSUME_TAC);;
e(ASM_SIMP_TAC[set_fraction_list]);;
e(SUBGOAL_THEN` (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  ebits_num (P:posit) -
  1) =0`ASSUME_TAC);;
 e(SUBGOAL_THEN`exp_length (P:posit)
 (APPEND [F]
 (APPEND (regime_bits (x:real) (P:posit))
 (APPEND (exp_list (x:real) (P:posit))
 (set_fraction_list (x:real) (P:posit))))) <= ebits_num P`ASSUME_TAC);;
e(IMP_REWRITE_TAC[PST_EXP_LENGTH]);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(UNDISCH_TAC`fraction_residue_set1 (x:real) (P:posit) < &1 / &2`);;
e(ASM_SIMP_TAC[GSYM REAL_NOT_LE]);;
e(ASM_SIMP_TAC[real_gt;REAL_LE_LT;DE_MORGAN_THM]);;
 e(ASM_SIMP_TAC[frac_posit_down]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[fraction_list]);;
e(ASM_SIMP_TAC[BV_n]);;



e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (real_to_posit_check3 (x:real) (P:posit))`);;
e(ASM_SIMP_TAC[real_to_posit_check3]);;
 e(ASM_SIMP_TAC[fraction_rounding1;SIGN_REAL_DECODE]);;
e(UNDISCH_TAC`fraction_residue_set1 (x:real) (P:posit) < &1 / &2`);;
e(ASM_SIMP_TAC[GSYM REAL_NOT_LE]);;
e(ASM_SIMP_TAC[real_gt;REAL_LE_LT;DE_MORGAN_THM]);;
 e(ASM_SIMP_TAC[frac_posit_down]);;
e(ASM_SIMP_TAC[FRAC_LENGTH;LENGTH_FRAC]);;
 e(REPEAT STRIP_TAC);;
e(SUBGOAL_THEN` exp_length P
   (APPEND [F]
   (APPEND (regime_bits x P)
   (APPEND (exp_list x P)
   (set_fraction_list x P )))) = ebits_num P`ASSUME_TAC);;
 e(IMP_REWRITE_TAC[EXP_LENGTH_EQ2]);;
e(UNDISCH_TAC`~exponential_round_check1 x P`);;
e(ASM_SIMP_TAC[exponential_round_check1]);;
e(ASM_ARITH_TAC);;
e(ASM_SIMP_TAC[set_fraction_list;LENGTH_FRAC]);;
e(SIMP_TAC[ARITH_RULE`(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit)) + ebits_num (P:posit) + 1)) = 
(nbits_num (P:posit) -
  (LENGTH (regime_bits (x:real) (P:posit))) - ebits_num (P:posit) - 1)`]);;
e(ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL]);;
e(DISJ1_TAC);;
e(IMP_REWRITE_TAC[LIST_EQ;REAL_OF_NUM_EQ]);;
e(ASM_REWRITE_TAC[pick_elements;GSYM ADD1]);;
e(ASM_SIMP_TAC[ARITH_RULE`(LENGTH (regime_bits (x:real) (P:posit)) + SUC (ebits_num (P:posit)))
= SUC (LENGTH (regime_bits (x:real) (P:posit)) + (ebits_num (P:posit)))`]);;
e(IMP_REWRITE_TAC[L_ADD1;TL;APPEND]);;
e(UNDISCH_TAC`is_valid_posit_length (P:posit)
      (APPEND [F]
      (APPEND (regime_bits (x:real) (P:posit))
      (APPEND (exp_list (x:real) (P:posit))
      (set_fraction_list (x:real) (P:posit)))))`);;
e(ASM_SIMP_TAC[is_valid_posit_length;LENGTH_APPEND;LENGTH;ADD1]);;
e(STRIP_TAC);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  1 -((LENGTH (regime_bits (x:real) (P:posit)) + ebits_num (P:posit)) + 1) +
  1)= (nbits_num (P:posit) - LENGTH (regime_bits (x:real) (P:posit)) -
 ebits_num (P:posit) - 1)`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
e(SUBGOAL_THEN`(ebits_num (P:posit)) = LENGTH (exp_list (x:real) (P:posit))`ASSUME_TAC);;
e(ASM_SIMP_TAC[exp_list;LENGTH_NUM_BV_f]);;
 e(ASM_SIMP_TAC[]);;
e(SUBGOAL_THEN`(nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1) = LENGTH (fraction_list
 ((x:real) /
  (scale_factor_r (P:posit) (CONS (sign_real x) (regime_bits x P)) *
   &2 pow BV_n (exp_list (x:real) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1))`ASSUME_TAC);;
e(ASM_SIMP_TAC[LENGTH_FRAC;EQ_SYM_EQ]);;
e(SUBGOAL_THEN`0 < LENGTH (fraction_list
 ((x:real) /
  (scale_factor_r (P:posit) (CONS (sign_real x) (regime_bits x P)) *
   &2 pow BV_n (exp_list (x:real) (P:posit))) -
  &1)
 (nbits_num (P:posit) -
  LENGTH (regime_bits (x:real) (P:posit)) -
  LENGTH (exp_list (x:real) (P:posit)) -
  1))`ASSUME_TAC);;
e(ASM_ARITH_TAC);;
 e(ASM_MESON_TAC[FRTH_LIST_APPEND]);;
let FRAC_DOWN_FRAC = top_thm();;
