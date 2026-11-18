import work_in_progress.GroupedResidualRecurrence
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Finite grouped-residual certificates, with publication and native geometry
kept distinct. The per-stage inventory is arithmetic data; identifying it with
an emitted framed word is a separate compiler obligation. No RAM.Can program
or constant-density executor is inferred from these facts alone. -/

namespace FourierSchur.OriginalGroupedResidualCertificate

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def edgeRank (h stage : ℕ) : Fin 10 → ℕ :=
  let b := h^stage-1
  ![b*(h-1), h-1, b*h, h, h^3-h^(stage+1),
    b, b*(h-1)+1, h-2, 1, h^3-h^(stage+1)]

def edgeCount (h v d : ℕ) : Fin 10 → ℕ :=
  ![2*v^3, 2*v^3, v^2*(h+1), 3*v^2*(h+1), v^2*(h+1),
    v^3*d, v^3*d, v^3*d, v^3*d, v^3*d]

def histogram (h v d rank : ℕ) : ℕ :=
  ∑ stage : Fin 3, ∑ family : Fin 10,
    if edgeRank h stage.val family=rank then edgeCount h v d family else 0

def rho100 : Fin 12 → ℕ :=
  ![1,98,99,100,9801,9802,9900,9999,989901,989902,990000,999900]
def count100 : Fin 12 → ℕ :=
  ![2498398374422412000000,1873798780816809000000,624624961318281000000,
    23767523010000,8455904226000000,624599593605603000000,
    2640835890000,624599593605603000000,8455904226000000,
    624599593605603000000,624599596246438890000,624599598887274780000]
def roles100 : ℕ := 1873807244643542670000
def order100 : ℕ := 1000000
def saving100 : ℕ := 6871402692000000
def padded100 : ℕ := 2^71

def rho32 : Fin 12 → ℕ :=
  ![1,30,31,32,961,962,992,1023,31713,31714,31744,32736]
def count32 : Fin 12 → ℕ :=
  ![804687153984000,603515365488000,201573328992000,4895629200,
    133846832000,201171788496000,543958800,201171788496000,
    133846832000,201171788496000,201172332454800,201172876413600]
def roles32 : ℕ := 603650844196400
def order32 : ℕ := 32768
def saving32 : ℕ := 29406742400
def physical32 : ℕ := 815262685588400
def padded32 : ℕ := 2^50

theorem histogram100 (i : Fin 12) :
    histogram 100 161700 147731 (rho100 i)=count100 i := by
  fin_cases i <;> norm_num [histogram,edgeRank,edgeCount,rho100,count100,Fin.sum_univ_succ]

theorem histogram32 (i : Fin 12) :
    histogram 32 4060 3006 (rho32 i)=count32 i := by
  fin_cases i <;> norm_num [histogram,edgeRank,edgeCount,rho32,count32,Fin.sum_univ_succ]

theorem ranges100 (i : Fin 12) : 0<rho100 i ∧ rho100 i<order100 ∧ 0<count100 i := by
  fin_cases i <;> norm_num [rho100,count100,order100]

theorem ranges32 (i : Fin 12) : 0<rho32 i ∧ rho32 i<order32 ∧ 0<count32 i := by
  fin_cases i <;> norm_num [rho32,count32,order32]

theorem total_count100 : (∑ i, count100 i)=8119837030724835570000 := by
  norm_num [count100,Fin.sum_univ_succ]

theorem first_moment100 : (∑ i, count100 i*rho100 i)+saving100=roles100*order100 := by
  norm_num [count100,rho100,saving100,roles100,order100,Fin.sum_univ_succ]

theorem first_moment32 : (∑ i, count32 i*rho32 i)+saving32=roles32*order32 := by
  norm_num [count32,rho32,saving32,roles32,order32,Fin.sum_univ_succ]

theorem native_geometry_counts :
    roles32=2*4060^3+3*4060^2*(4060*3006+33) ∧
    physical32=2*4060^3+3*4060^2*(4060^2+33) ∧
    saving32=2*4060^2*(4060-3*32*33) ∧
    physical32-roles32=211611841392000 ∧
    padded32-physical32=310637221254224 ∧
    padded32-roles32=522249062646224 := by
  norm_num [roles32,physical32,saving32,padded32]

def epsilonG : ℝ := 1/12500000000
def alphaG : ℝ := 1-epsilonG
def epsilon32 : ℝ := 1/100000000
def alpha32 : ℝ := 1-epsilon32

theorem exponents_pos_lt : 0<alphaG ∧ alphaG<1 ∧ 0<alpha32 ∧ alpha32<1 := by
  norm_num [alphaG,epsilonG,alpha32,epsilon32]

theorem rational_gap100 :
    (73:ℝ)/19906842167500-epsilonG*(21/500)/(1-14*epsilonG)=
      25470875981/82945175605018069885000 := by
  norm_num [epsilonG]

theorem padded_gap100 :
    (roles100:ℝ)/(padded100:ℝ)*
      ((73:ℝ)/19906842167500-epsilonG*(21/500)/(1-14*epsilonG))=
      599385773230964181/2459565873739893100459373625344 := by
  norm_num [roles100,padded100,epsilonG]

theorem rational_gap32 :
    (223:ℝ)/150000840704-epsilon32*(90206168227/750004203520)/(1-11*epsilon32)=
      409496529/1442315617345264640 := by
  norm_num [epsilon32]

theorem padded_gap32 :
    (roles32:ℝ)/(padded32:ℝ)*
      ((223:ℝ)/150000840704-epsilon32*(90206168227/750004203520)/(1-11*epsilon32))=
      1096871260131465/7205758611159259182792704 := by
  norm_num [roles32,padded32,epsilon32]

theorem rational_gaps_positive :
    (0:ℝ)<25470875981/82945175605018069885000 ∧
    (0:ℝ)<599385773230964181/2459565873739893100459373625344 ∧
    (0:ℝ)<409496529/1442315617345264640 ∧
    (0:ℝ)<1096871260131465/7205758611159259182792704 := by norm_num

def point100 (i : Fin 12) : ℝ := (rho100 i:ℝ)/(order100:ℝ)
def weight100 (i : Fin 12) : ℝ := (count100 i:ℝ)/(roles100:ℝ)
def point32 (i : Fin 12) : ℝ := (rho32 i:ℝ)/(order32:ℝ)
def weight32 (i : Fin 12) : ℝ := (count32 i:ℝ)/(roles32:ℝ)

def moment (w x : Fin 12 → ℝ) (z : ℝ) : ℝ := ∑ i, w i*(x i)^z
def firstMoment (w x : Fin 12 → ℝ) : ℝ := ∑ i, w i*x i
def logMoment (w x : Fin 12 → ℝ) : ℝ := ∑ i, w i*(x i*Real.log (1/x i))

theorem point100_pos_le (i : Fin 12) : 0<point100 i ∧ point100 i≤1 := by
  fin_cases i <;> norm_num [point100,rho100,order100]
theorem point32_pos_le (i : Fin 12) : 0<point32 i ∧ point32 i≤1 := by
  fin_cases i <;> norm_num [point32,rho32,order32]
theorem weight100_nonneg (i : Fin 12) : 0≤weight100 i := by
  unfold weight100
  positivity
theorem weight32_nonneg (i : Fin 12) : 0≤weight32 i := by
  unfold weight32
  positivity

theorem firstMoment100_eq : firstMoment weight100 point100=1-(73:ℝ)/19906842167500 := by
  norm_num [firstMoment,weight100,point100,count100,rho100,roles100,order100,Fin.sum_univ_succ]
theorem firstMoment32_eq : firstMoment weight32 point32=1-(223:ℝ)/150000840704 := by
  norm_num [firstMoment,weight32,point32,count32,rho32,roles32,order32,Fin.sum_univ_succ]

theorem log_two_upper : Real.log 2≤(7:ℝ)/10 :=
  Real.log_two_lt_d9.le.trans (by norm_num)

theorem log_million_upper : Real.log (1000000:ℝ)≤14 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<1000000)
    (by norm_num : (1000000:ℝ)≤(2:ℝ)^20)
  rw [Real.log_pow] at hh
  norm_num at hh
  nlinarith [log_two_upper]

theorem log_mid100_upper : Real.log ((1000000:ℝ)/9801)≤5 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<1000000/9801)
    (by norm_num : (1000000:ℝ)/9801≤(2:ℝ)^7)
  rw [Real.log_pow] at hh
  nlinarith [log_two_upper]

theorem log_order32_upper : Real.log (32768:ℝ)≤11 := by
  rw [show (32768:ℝ)=(2:ℝ)^15 by norm_num, Real.log_pow]
  norm_num
  nlinarith [log_two_upper]

theorem log_mid32_upper : Real.log ((32768:ℝ)/961)≤(21:ℝ)/5 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<32768/961)
    (by norm_num : (32768:ℝ)/961≤(2:ℝ)^6)
  rw [Real.log_pow] at hh
  nlinarith [log_two_upper]

theorem log_ratio_upper (u r : ℕ) (hu : 0<u) (hr : 0<r) (L : ℝ)
    (hL : Real.log (u:ℝ)≤L) : Real.log (1/((r:ℝ)/(u:ℝ)))≤L := by
  have hu' : (0:ℝ)<u := by exact_mod_cast hu
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have h1 : (1:ℝ)≤r := by exact_mod_cast hr
  have he : 1/((r:ℝ)/(u:ℝ))=(u:ℝ)/(r:ℝ) := by field_simp
  rw [he]
  have hb : (u:ℝ)/(r:ℝ)≤u := (div_le_iff₀ hr').mpr (by nlinarith)
  exact (Real.log_le_log (div_pos hu' hr') hb).trans hL

theorem log100_upper (i : Fin 12) : Real.log (1/point100 i)≤14 :=
  log_ratio_upper order100 (rho100 i) (by norm_num [order100])
    (ranges100 i).1 14 log_million_upper
theorem log32_upper (i : Fin 12) : Real.log (1/point32 i)≤11 :=
  log_ratio_upper order32 (rho32 i) (by norm_num [order32])
    (ranges32 i).1 11 log_order32_upper

theorem log_reciprocal_moment_le (x : ℝ) (hx : 0<x) :
    x*Real.log (1/x)≤1-x := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (one_div_pos.mpr hx)) hx.le
  have he : x*(1/x-1)=1-x := by field_simp
  exact hh.trans_eq he

theorem log_mid100 (i : Fin 12) (hi : 9801≤rho100 i) :
    Real.log (1/point100 i)≤5 := by
  have hr : (0:ℝ)<rho100 i := by exact_mod_cast (ranges100 i).1
  have hlow : (9801:ℝ)≤rho100 i := by exact_mod_cast hi
  have he : 1/point100 i=(1000000:ℝ)/(rho100 i:ℝ) := by
    unfold point100 order100
    norm_num
  rw [he]
  have hb : (1000000:ℝ)/(rho100 i:ℝ)≤1000000/9801 :=
    (div_le_div_iff₀ hr (by norm_num)).mpr (by nlinarith)
  exact (Real.log_le_log (div_pos (by norm_num) hr) hb).trans log_mid100_upper

theorem log_mid32 (i : Fin 12) (hi : 961≤rho32 i) :
    Real.log (1/point32 i)≤(21:ℝ)/5 := by
  have hr : (0:ℝ)<rho32 i := by exact_mod_cast (ranges32 i).1
  have hlow : (961:ℝ)≤rho32 i := by exact_mod_cast hi
  have he : 1/point32 i=(32768:ℝ)/(rho32 i:ℝ) := by
    unfold point32 order32
    norm_num
  rw [he]
  have hb : (32768:ℝ)/(rho32 i:ℝ)≤32768/961 :=
    (div_le_div_iff₀ hr (by norm_num)).mpr (by nlinarith)
  exact (Real.log_le_log (div_pos (by norm_num) hr) hb).trans log_mid32_upper

def cap100 (i : Fin 12) : ℝ :=
  if rho100 i≤100 then 14*point100 i
  else if rho100 i≤9999 then 5*point100 i else 1-point100 i
def cap32 (i : Fin 12) : ℝ :=
  if rho32 i≤32 then 11*point32 i
  else if rho32 i≤1023 then (21/5)*point32 i else 1-point32 i

theorem point_cap100 (i : Fin 12) : point100 i*Real.log (1/point100 i)≤cap100 i := by
  unfold cap100
  split_ifs with hs hm
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left (log100_upper i) (point100_pos_le i).1.le
  · have hi : 9801≤rho100 i := by fin_cases i <;> norm_num [rho100] at *
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (log_mid100 i hi) (point100_pos_le i).1.le
  · exact log_reciprocal_moment_le _ (point100_pos_le i).1

theorem point_cap32 (i : Fin 12) : point32 i*Real.log (1/point32 i)≤cap32 i := by
  unfold cap32
  split_ifs with hs hm
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left (log32_upper i) (point32_pos_le i).1.le
  · have hi : 961≤rho32 i := by fin_cases i <;> norm_num [rho32] at *
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (log_mid32 i hi) (point32_pos_le i).1.le
  · exact log_reciprocal_moment_le _ (point32_pos_le i).1

theorem cap_sum100 : (∑ i, weight100 i*cap100 i)=1655735581771/39813684335000 := by
  norm_num [weight100,cap100,point100,rho100,count100,roles100,order100,Fin.sum_univ_succ]
theorem cap_sum32 : (∑ i, weight32 i*cap32 i)=90206168227/750004203520 := by
  norm_num [weight32,cap32,point32,rho32,count32,roles32,order32,Fin.sum_univ_succ]

theorem logMoment100_bound : logMoment weight100 point100≤(21:ℝ)/500 := by
  have hh : logMoment weight100 point100≤∑ i, weight100 i*cap100 i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (point_cap100 i) (weight100_nonneg i)
  rw [cap_sum100] at hh
  exact hh.trans (by norm_num)

theorem logMoment32_bound :
    logMoment weight32 point32≤(90206168227:ℝ)/750004203520 := by
  have hh : logMoment weight32 point32≤∑ i, weight32 i*cap32 i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (point_cap32 i) (weight32_nonneg i)
  simpa only [cap_sum32] using hh

theorem exp_geometric_bound (y : ℝ) (hy : y<1) :
    Real.exp y-1≤y/(1-y) := by
  have hd : 0<1-y := by linarith
  have hlog := Real.log_le_sub_one_of_pos hd
  have hb : y≤-Real.log (1-y) := by linarith
  have he := Real.exp_le_exp.mpr hb
  rw [Real.exp_neg,Real.exp_log hd] at he
  have hm : Real.exp y*(1-y)≤1 := by
    apply (le_div_iff₀ hd).mp
    simpa only [one_div] using he
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem rpow_perturb_bound (x e L : ℝ) (hx : 0<x) (hx1 : x≤1)
    (he : 0≤e) (hL : Real.log (1/x)≤L) (hsmall : L*e<1) :
    x^(1-e)≤x+e*(x*Real.log (1/x))/(1-L*e) := by
  let y := e*Real.log (1/x)
  have hl0 : 0≤Real.log (1/x) := Real.log_nonneg
    ((le_div_iff₀ hx).mpr (by simpa using hx1))
  have hy0 : 0≤y := mul_nonneg he hl0
  have hyL : y≤L*e := by dsimp [y]; nlinarith [mul_le_mul_of_nonneg_left hL he]
  have hy : y<1 := hyL.trans_lt hsmall
  have hd : 0<1-L*e := by linarith
  have hden : 1-L*e≤1-y := by linarith
  have hb := exp_geometric_bound y hy
  have hbmul : (Real.exp y-1)*(1-y)≤y := (le_div_iff₀ (by linarith : 0<1-y)).mp hb
  have hnn : 0≤Real.exp y-1 := by have := Real.one_le_exp hy0; linarith
  have hm : (Real.exp y-1)*(1-L*e)≤y :=
    (mul_le_mul_of_nonneg_left hden hnn).trans hbmul
  have hf : Real.exp y-1≤y/(1-L*e) := (le_div_iff₀ hd).mpr hm
  have hprod := mul_le_mul_of_nonneg_left hf hx.le
  have hlog : Real.log (1/x)=-Real.log x := by simp [one_div,Real.log_inv]
  have hexp : Real.log x*(1-e)=Real.log x+y := by dsimp [y]; rw [hlog]; ring
  rw [Real.rpow_def_of_pos hx,hexp,Real.exp_add,Real.exp_log hx]
  calc
    x*Real.exp y=x+x*(Real.exp y-1) := by ring
    _≤x+x*(y/(1-L*e)) := add_le_add_right hprod _
    _=x+e*(x*Real.log (1/x))/(1-L*e) := by dsimp [y]; ring

theorem moment_perturb_bound (w x : Fin 12 → ℝ) (e L : ℝ)
    (hw : ∀ i, 0≤w i) (hx : ∀ i, 0<x i ∧ x i≤1)
    (he : 0≤e) (hL : ∀ i, Real.log (1/x i)≤L) (hsmall : L*e<1) :
    moment w x (1-e)≤firstMoment w x+e*logMoment w x/(1-L*e) := by
  have hh : moment w x (1-e)≤∑ i, w i*(x i+e*(x i*Real.log (1/x i))/(1-L*e)) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (rpow_perturb_bound _ _ _ (hx i).1 (hx i).2 he (hL i) hsmall) (hw i)
  refine hh.trans_eq ?_
  calc
    _=(∑ i, w i*x i)+(∑ i, (e/(1-L*e))*(w i*(x i*Real.log (1/x i)))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=firstMoment w x+e*logMoment w x/(1-L*e) := by
      rw [← Finset.mul_sum]
      unfold firstMoment logMoment
      ring

theorem moment100_alphaG_lt : moment weight100 point100 alphaG<1 := by
  have hh := moment_perturb_bound weight100 point100 epsilonG 14
    weight100_nonneg point100_pos_le (by norm_num [epsilonG]) log100_upper (by norm_num [epsilonG])
  change moment weight100 point100 alphaG≤_ at hh
  rw [firstMoment100_eq] at hh
  have he : 0≤epsilonG := by norm_num [epsilonG]
  have hd : 0≤1-14*epsilonG := by norm_num [epsilonG]
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left logMoment100_bound he) hd
  have ht := hh.trans (add_le_add_right hc _)
  exact ht.trans_lt (by norm_num [epsilonG])

theorem moment32_alpha32_lt : moment weight32 point32 alpha32<1 := by
  have hh := moment_perturb_bound weight32 point32 epsilon32 11
    weight32_nonneg point32_pos_le (by norm_num [epsilon32]) log32_upper (by norm_num [epsilon32])
  change moment weight32 point32 alpha32≤_ at hh
  rw [firstMoment32_eq] at hh
  have he : 0≤epsilon32 := by norm_num [epsilon32]
  have hd : 0≤1-11*epsilon32 := by norm_num [epsilon32]
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left logMoment32_bound he) hd
  have ht := hh.trans (add_le_add_right hc _)
  exact ht.trans_lt (by norm_num [epsilon32])

theorem moment32_alphaG_lt : moment weight32 point32 alphaG<1 := by
  have ha : alpha32≤alphaG := by norm_num [alpha32,epsilon32,alphaG,epsilonG]
  have hh : moment weight32 point32 alphaG≤moment weight32 point32 alpha32 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (point32_pos_le i).1 (point32_pos_le i).2 ha)
      (weight32_nonneg i)
  exact hh.trans_lt moment32_alpha32_lt

def padding100 : ℝ := ((padded100-roles100:ℕ):ℝ)/(padded100:ℝ)
def paddedWeight100 (i : Fin 12) : ℝ := (count100 i:ℝ)/(padded100:ℝ)
def paddedMoment100 (z : ℝ) : ℝ := padding100+moment paddedWeight100 point100 z
def padding32 : ℝ := ((padded32-roles32:ℕ):ℝ)/(padded32:ℝ)
def paddedWeight32 (i : Fin 12) : ℝ := (count32 i:ℝ)/(padded32:ℝ)
def paddedMoment32 (z : ℝ) : ℝ := padding32+moment paddedWeight32 point32 z

theorem paddedMoment100_factor (z : ℝ) :
    paddedMoment100 z=(1-(roles100:ℝ)/(padded100:ℝ))+
      (roles100:ℝ)/(padded100:ℝ)*moment weight100 point100 z := by
  unfold paddedMoment100 moment
  rw [Finset.mul_sum]
  congr 1
  · norm_num [padding100,roles100,padded100]
  · apply Finset.sum_congr rfl
    intro i _
    unfold paddedWeight100 weight100
    norm_num [roles100,padded100]
    ring

theorem paddedMoment32_factor (z : ℝ) :
    paddedMoment32 z=(1-(roles32:ℝ)/(padded32:ℝ))+
      (roles32:ℝ)/(padded32:ℝ)*moment weight32 point32 z := by
  unfold paddedMoment32 moment
  rw [Finset.mul_sum]
  congr 1
  · norm_num [padding32,roles32,padded32]
  · apply Finset.sum_congr rfl
    intro i _
    unfold paddedWeight32 weight32
    norm_num [roles32,padded32]
    ring

theorem padded_weights_nonneg :
    0≤padding100 ∧ 0≤padding32 ∧
    (∀ i, 0≤paddedWeight100 i) ∧ (∀ i, 0≤paddedWeight32 i) := by
  refine ⟨by norm_num [padding100,padded100,roles100],
    by norm_num [padding32,padded32,roles32], ?_, ?_⟩
  · intro i
    unfold paddedWeight100
    positivity
  · intro i
    unfold paddedWeight32
    positivity

theorem paddedMoment100_alphaG_lt : paddedMoment100 alphaG<1 := by
  rw [paddedMoment100_factor]
  exact GroupedResidualRecurrence.padding_contraction _ _
    (by norm_num [roles100,padded100]) moment100_alphaG_lt

theorem paddedMoment32_alpha32_lt : paddedMoment32 alpha32<1 := by
  rw [paddedMoment32_factor]
  exact GroupedResidualRecurrence.padding_contraction _ _
    (by norm_num [roles32,padded32]) moment32_alpha32_lt

theorem paddedMoment32_alphaG_lt : paddedMoment32 alphaG<1 := by
  rw [paddedMoment32_factor]
  exact GroupedResidualRecurrence.padding_contraction _ _
    (by norm_num [roles32,padded32]) moment32_alphaG_lt

theorem total_count32 : (∑ i, count32 i)=2615909556072400 := by
  norm_num [count32,Fin.sum_univ_succ]

theorem paddedMoment100_zero :
    paddedMoment100 0=268975407109878609589/73786976294838206464 := by
  norm_num [paddedMoment100,moment,padding100,paddedWeight100,
    count100,roles100,padded100,Fin.sum_univ_succ]

theorem paddedMoment32_zero :
    paddedMoment32 0=98067456834957/35184372088832 := by
  norm_num [paddedMoment32,moment,padding32,paddedWeight32,
    count32,roles32,padded32,Fin.sum_univ_succ]

theorem zero_moments_gt_one : 1<paddedMoment100 0 ∧ 1<paddedMoment32 0 := by
  rw [paddedMoment100_zero,paddedMoment32_zero]
  norm_num

def lower100 : Fin 12 → ℝ :=
  ![0,9/1000,0,0,0,99/1000,0,99/1000,0,994/1000,994/1000,999/1000]

theorem lower100_square (i : Fin 12) : 0≤lower100 i ∧ (lower100 i)^2≤point100 i := by
  fin_cases i <;> norm_num [lower100,point100,rho100,order100]

theorem lower100_le_half (i : Fin 12) : lower100 i≤(point100 i)^((1:ℝ)/2) := by
  have hh := (Real.le_rpow_inv_iff_of_pos (lower100_square i).1
    (point100_pos_le i).1.le (show (0:ℝ)<2 by norm_num)).mpr
    (by simpa only [Real.rpow_two] using (lower100_square i).2)
  simpa only [one_div] using hh

theorem half100_witness_sum :
    (∑ i, weight100 i*lower100 i)=9591073271824/8958078975375 := by
  norm_num [weight100,lower100,count100,roles100,Fin.sum_univ_succ]

theorem moment100_half_gt_one : 1<moment weight100 point100 ((1:ℝ)/2) := by
  have hh : (∑ i, weight100 i*lower100 i)≤moment weight100 point100 ((1:ℝ)/2) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (lower100_le_half i) (weight100_nonneg i)
  rw [half100_witness_sum] at hh
  exact lt_of_lt_of_le (by norm_num) hh

theorem paddedMoment100_half_gt_one : 1<paddedMoment100 ((1:ℝ)/2) := by
  rw [paddedMoment100_factor]
  have hw : (0:ℝ)<(roles100:ℝ)/(padded100:ℝ) := by norm_num [roles100,padded100]
  have hh := mul_lt_mul_of_pos_left moment100_half_gt_one hw
  nlinarith

end
end FourierSchur.OriginalGroupedResidualCertificate
