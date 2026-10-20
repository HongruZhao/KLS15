import TripleCreationExactCap

/-! Draft proof cache only: every value is proved from exactCap_step.
No new numerical premise or native evaluation axiom is introduced.
No compilation or performance measurement was performed. -/
noncomputable section
namespace KLSConstantImprovement.TripleCreationExactCapMemo
open KLSBelow25.TripleCreation
set_option maxHeartbeats 0

@[simp] theorem cap_0 : exactCap 0=(0 : ℝ) := by
  norm_num [exactCap]

@[simp] theorem cap_1 : exactCap 1=(0 : ℝ) := by
  norm_num [exactCap]

@[simp] theorem cap_2 : exactCap 2=(0 : ℝ) := by
  norm_num [exactCap]

@[simp] theorem cap_3 : exactCap 3=(864 : ℝ) := by
  norm_num [exactCap]

@[simp] theorem cap_4 : exactCap 4=(13824 : ℝ) := by
  norm_num [exactCap]

@[simp] theorem cap_5 : exactCap 5=(61560 : ℝ) := by
  rw [exactCap_step 5 (by norm_num),cap_3]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_6 : exactCap 6=(196560 : ℝ) := by
  rw [exactCap_step 6 (by norm_num),cap_4]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_7 : exactCap 7=(501984 : ℝ) := by
  rw [exactCap_step 7 (by norm_num),cap_5]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_8 : exactCap 8=(1109808 : ℝ) := by
  rw [exactCap_step 8 (by norm_num),cap_6]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_9 : exactCap 9=(11017296/5 : ℝ) := by
  rw [exactCap_step 9 (by norm_num),cap_7]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_10 : exactCap 10=(4039470 : ℝ) := by
  rw [exactCap_step 10 (by norm_num),cap_8]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_11 : exactCap 11=(48639096/7 : ℝ) := by
  rw [exactCap_step 11 (by norm_num),cap_9]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_12 : exactCap 12=(22723173/2 : ℝ) := by
  rw [exactCap_step 12 (by norm_num),cap_10]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_13 : exactCap 13=(623330136/35 : ℝ) := by
  rw [exactCap_step 13 (by norm_num),cap_11]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_14 : exactCap 14=(1078148799/40 : ℝ) := by
  rw [exactCap_step 14 (by norm_num),cap_12]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_15 : exactCap 15=(39583440 : ℝ) := by
  rw [exactCap_step 15 (by norm_num),cap_13]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_16 : exactCap 16=(226609839/4 : ℝ) := by
  rw [exactCap_step 16 (by norm_num),cap_14]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_17 : exactCap 17=(554907744/7 : ℝ) := by
  rw [exactCap_step 17 (by norm_num),cap_15]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_18 : exactCap 18=(243615701817/2240 : ℝ) := by
  rw [exactCap_step 18 (by norm_num),cap_16]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_19 : exactCap 19=(733052376/5 : ℝ) := by
  rw [exactCap_step 19 (by norm_num),cap_17]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_20 : exactCap 20=(697370622525/3584 : ℝ) := by
  rw [exactCap_step 20 (by norm_num),cap_18]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_21 : exactCap 21=(254635416 : ℝ) := by
  rw [exactCap_step 21 (by norm_num),cap_19]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_22 : exactCap 22=(673868838555/2048 : ℝ) := by
  rw [exactCap_step 22 (by norm_num),cap_20]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_23 : exactCap 23=(2101543488/5 : ℝ) := by
  rw [exactCap_step 23 (by norm_num),cap_21]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_24 : exactCap 24=(7616750832801/14336 : ℝ) := by
  rw [exactCap_step 24 (by norm_num),cap_22]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_25 : exactCap 25=(4656258000/7 : ℝ) := by
  rw [exactCap_step 25 (by norm_num),cap_23]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_26 : exactCap 26=(13524673631625/16384 : ℝ) := by
  rw [exactCap_step 26 (by norm_num),cap_24]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_27 : exactCap 27=(7112678040/7 : ℝ) := by
  rw [exactCap_step 27 (by norm_num),cap_25]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_28 : exactCap 28=(81353179474749/65536 : ℝ) := by
  rw [exactCap_step 28 (by norm_num),cap_26]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_29 : exactCap 29=(7529822856/5 : ℝ) := by
  rw [exactCap_step 29 (by norm_num),cap_27]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_30 : exactCap 30=(475829217010215/262144 : ℝ) := by
  rw [exactCap_step 30 (by norm_num),cap_28]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_31 : exactCap 31=(15221824848/7 : ℝ) := by
  rw [exactCap_step 31 (by norm_num),cap_29]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_32 : exactCap 32=(1188337186353393/458752 : ℝ) := by
  rw [exactCap_step 32 (by norm_num),cap_30]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_33 : exactCap 33=(15346571328/5 : ℝ) := by
  rw [exactCap_step 33 (by norm_num),cap_31]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_34 : exactCap 34=(265612648342362849/73400320 : ℝ) := by
  rw [exactCap_step 34 (by norm_num),cap_32]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_35 : exactCap 35=(4246343640 : ℝ) := by
  rw [exactCap_step 35 (by norm_num),cap_33]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_36 : exactCap 36=(166457457430176231/33554432 : ℝ) := by
  rw [exactCap_step 36 (by norm_num),cap_34]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_37 : exactCap 37=(5771254968 : ℝ) := by
  rw [exactCap_step 37 (by norm_num),cap_35]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_38 : exactCap 38=(31415481536708832993/4697620480 : ℝ) := by
  rw [exactCap_step 38 (by norm_num),cap_36]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_39 : exactCap 39=(270207037152/35 : ℝ) := by
  rw [exactCap_step 39 (by norm_num),cap_37]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_40 : exactCap 40=(1191937275593483445/134217728 : ℝ) := by
  rw [exactCap_step 40 (by norm_num),cap_38]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_41 : exactCap 41=(71266304304/7 : ℝ) := by
  rw [exactCap_step 41 (by norm_num),cap_39]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_42 : exactCap 42=(12491916993579323853/1073741824 : ℝ) := by
  rw [exactCap_step 42 (by norm_num),cap_40]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_43 : exactCap 43=(66268588968/5 : ℝ) := by
  rw [exactCap_step 43 (by norm_num),cap_41]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_44 : exactCap 44=(323298844193136413151/21474836480 : ℝ) := by
  rw [exactCap_step 44 (by norm_num),cap_42]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_45 : exactCap 45=(119369515320/7 : ℝ) := by
  rw [exactCap_step 45 (by norm_num),cap_43]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_46 : exactCap 46=(2316718627288202275083/120259084288 : ℝ) := by
  rw [exactCap_step 46 (by norm_num),cap_44]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_47 : exactCap 47=(21707189136 : ℝ) := by
  rw [exactCap_step 47 (by norm_num),cap_45]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_48 : exactCap 48=(7335764778236008410657/300647710720 : ℝ) := by
  rw [exactCap_step 48 (by norm_num),cap_46]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_49 : exactCap 49=(136810802016/5 : ℝ) := by
  rw [exactCap_step 49 (by norm_num),cap_47]
  norm_num [forcing,recurrenceMultiplier]

@[simp] theorem cap_50 : exactCap 50=(4207691504743847119125/137438953472 : ℝ) := by
  rw [exactCap_step 50 (by norm_num),cap_48]
  norm_num [forcing,recurrenceMultiplier]

end KLSConstantImprovement.TripleCreationExactCapMemo
#print axioms KLSConstantImprovement.TripleCreationExactCapMemo.cap_50

#print axioms KLSConstantImprovement.TripleCreationExactCapMemo.cap_49
#print axioms KLSConstantImprovement.TripleCreationExactCapMemo.cap_50
