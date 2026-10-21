import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentProgram

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel
open HistoricalSearch

/-- Fast entry at 24 (base size 32): load the base word (unshifted for a 32-byte base), then
the exponent and modulus words from their fixed offsets 128 and 160. -/
def fastProgram : List Instr :=
  [.push 1 96, .op .CALLDATALOAD, .push 1 128, .op .CALLDATALOAD, .push 1 160, .op .CALLDATALOAD]

/-- Join point at 31: jump to the window core at 872 unless
`exponent = modulus - 1`, in which case fall through to the special-prime test at 40. -/
def joinProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .op .NOT, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .push 1 1, .op .LT, .push 2 745, .op .JUMPI]

/-- General-width entry at 103 (exponent and modulus sizes 32, base size not 32):
a base size above 32 leaves for the wide fallback at 238. -/
def genCheckProgram : List Instr :=
  [.op .JUMPDEST, .push 1 32, .push 0 0, .op .CALLDATALOAD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .push 1 219, .op .JUMPI]

/-- 112: with `k = 32 - baseSize`, push `k`, the base word shifted right by `8 k`, the exponent
word at `128 - k` and the modulus word at `160 - k`, then join at 33. -/
def genLoadProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .SUB,
   .push 1 96, .op .CALLDATALOAD, .op (.Dup ⟨1, by decide⟩), .push 1 3, .op .SHL, .op .SHR,
   .op (.Dup ⟨1, by decide⟩), .push 1 128, .op .SUB, .op .CALLDATALOAD,
   .op (.Dup ⟨2, by decide⟩), .push 1 160, .op .SUB, .op .CALLDATALOAD,
   .push 1 33, .op .JUMP]

/-- `modulus + ~exponent`, zero exactly when `exponent = modulus - 1` (mod 2^256). -/
def fermatDiff (modulus exponent : UInt256) : UInt256 :=
  modulus + UInt256.lnot exponent

theorem fermatDiff_zero (modulus exponent : UInt256)
    (h : (fermatDiff modulus exponent).toNat = 0) :
    modulus - UInt256.ofNat 1 = exponent := by
  apply Challenge.EvmProof.Word.word_ext
  rw [fermatDiff, Challenge.EvmProof.Word.word_toNat_add] at h
  have hl : (UInt256.lnot exponent).toNat = 2 ^ 256 - 1 - exponent.toNat := by
    have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - exponent.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl] at h
  rw [Challenge.EvmProof.Word.word_toNat_sub]
  have h1 : (UInt256.ofNat 1).toNat = 1 := by decide
  rw [h1]
  have hm : modulus.toNat < 2 ^ 256 := modulus.val.isLt
  have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
  omega

theorem fermatDiff_one (modulus exponent : UInt256)
    (h : (fermatDiff modulus exponent).toNat = 1) :
    modulus - UInt256.ofNat 2 = exponent := by
  apply Challenge.EvmProof.Word.word_ext
  rw [fermatDiff, Challenge.EvmProof.Word.word_toNat_add] at h
  have hl : (UInt256.lnot exponent).toNat = 2 ^ 256 - 1 - exponent.toNat := by
    have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - exponent.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl] at h
  rw [Challenge.EvmProof.Word.word_toNat_sub]
  have h2 : (UInt256.ofNat 2).toNat = 2 := by decide
  rw [h2]
  have hm : modulus.toNat < 2 ^ 256 := modulus.val.isLt
  have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
  omega

def jumpTailProgram : List Instr := [.push 2 745, .op .JUMP]
/-- At this guarded prime branch, the difference is either zero or one. Both
supported primes are odd, so the exponent low bit is exactly that difference.
Constructing the mask through PUSH0 ISZERO keeps every PC and instruction index
unchanged while saving one gas versus recomputing modulus + ~exponent. -/
def tailProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .push 0 0, .op .ISZERO, .op .AND,
   .push 2 9818, .op .JUMPI]

private theorem guardedParity_eq (modulus exponent : UInt256)
    (hsmall : (fermatDiff modulus exponent).toNat ≤ 1)
    (hprime : (FermatProgram.primeValue modulus).toNat ≠ 0) :
    UInt256.land (UInt256.ofNat 1) exponent = fermatDiff modulus exponent := by
  have hm := (FermatProgram.primeValue_nonzero modulus).mp hprime
  by_cases hz : (fermatDiff modulus exponent).toNat = 0
  · have he := fermatDiff_zero modulus exponent hz
    have hd : fermatDiff modulus exponent = UInt256.ofNat 0 :=
      Challenge.EvmProof.Word.word_ext hz
    rw [hd, ←he]
    rcases hm with rfl | rfl <;> decide
  · have ho : (fermatDiff modulus exponent).toNat = 1 := by omega
    have he := fermatDiff_one modulus exponent ho
    have hd : fermatDiff modulus exponent = UInt256.ofNat 1 :=
      Challenge.EvmProof.Word.word_ext ho
    rw [hd, ←he]
    rcases hm with rfl | rfl <;> decide
def inverseGuardProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .push 32 FermatProgram.bn, .op .XOR,
    .push 2 745, .op .JUMPI]
def inverseDiff (modulus : UInt256) : UInt256 := UInt256.xor FermatProgram.bn modulus

theorem inverseDiff_zero (modulus : UInt256) (h : (inverseDiff modulus).toNat = 0) :
    modulus = FermatProgram.bn := by
  have hw : inverseDiff modulus = 0 := Challenge.EvmProof.Word.word_ext h
  unfold inverseDiff at hw
  rw [WindowGuardLogic.wordXor_eq_zero_iff] at hw
  exact hw.symm

def primeValueProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 32 FermatProgram.bn, .op .EQ,
   .op (.Dup ⟨1, by decide⟩), .push 5 0x01000003d0, .op .NOT,
   .op .EQ, .op .OR]

def primeProgram : List Instr :=
  primeValueProgram ++ [.push 2 9800, .op .JUMPI]

set_option linter.unusedSimpArgs false in
theorem run_fast (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions fastProgram (framed template (UInt256.ofNat 24) rest) =
    some (framed template (UInt256.ofNat 33)
      (MachineState.readWord template.executionEnv.calldata 160 ::
        MachineState.readWord template.executionEnv.calldata 128 ::
        MachineState.readWord template.executionEnv.calldata 96 :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  have h128 : (UInt256.ofNat 128).toNat = 128 := by decide
  have h160 : (UInt256.ofNat 160).toNat = 160 := by decide
  simp [fastProgram, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
    hz, h96, h128, h160, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_join (template : State) (modulus exponent : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions joinProgram
      (framed template (UInt256.ofNat 33) (modulus :: exponent :: rest)) =
    some (framed template
      (if (fermatDiff modulus exponent).toNat ≤ 1 then UInt256.ofNat 45 else UInt256.ofNat 745)
      (modulus :: exponent :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  simp only [fermatDiff]
  have hcmp : UInt256.lt (UInt256.ofNat 1) (modulus + UInt256.lnot exponent) =
      (if (modulus + UInt256.lnot exponent).toNat ≤ 1 then UInt256.ofNat 0 else UInt256.ofNat 1) := by
    unfold UInt256.lt
    have h1 : (UInt256.ofNat 1).toNat = 1 := by decide
    rw [h1]
    split_ifs <;> simp_all <;> omega
  by_cases hz : (modulus + UInt256.lnot exponent).toNat ≤ 1 <;>
    simp (config := { maxSteps := 500000 }) [joinProgram, runInstructions, framed,
      htarget, hz, UInt256.isTrue, hcmp, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_gen_check (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 219 = true) :
    runInstructions genCheckProgram (framed template (UInt256.ofNat 101) rest) =
    some (framed template
      (if (UInt256.gt (MachineState.readWord template.executionEnv.calldata 0)
          (UInt256.ofNat 32)).toNat = 0 then UInt256.ofNat 112 else UInt256.ofNat 219)
      (MachineState.readWord template.executionEnv.calldata 0 :: UInt256.ofNat 32 :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  by_cases hv : (UInt256.gt (MachineState.readWord template.executionEnv.calldata 0)
      (UInt256.ofNat 32)).toNat = 0 <;>
    simp (config := { maxSteps := 500000 }) [genCheckProgram, runInstructions, framed,
      htarget, hv, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      hz, h0,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_gen_load (template : State) (b : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 33 = true) :
    runInstructions genLoadProgram
      (framed template (UInt256.ofNat 112) (b :: UInt256.ofNat 32 :: rest)) =
    some (framed template (UInt256.ofNat 33)
      (MachineState.readWord template.executionEnv.calldata
          (UInt256.ofNat 160 - (UInt256.ofNat 32 - b)).toNat ::
        MachineState.readWord template.executionEnv.calldata
          (UInt256.ofNat 128 - (UInt256.ofNat 32 - b)).toNat ::
        UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
          (UInt256.shiftLeft (UInt256.ofNat 32 - b) (UInt256.ofNat 3)) ::
        (UInt256.ofNat 32 - b) :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  simp (config := { maxSteps := 500000 }) [genLoadProgram, runInstructions, framed,
    htarget, List.exchange, h96, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prime (template : State) (modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 9800 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 45) (modulus :: rest)) =
    some (framed template
      (if (FermatProgram.primeValue modulus).toNat = 0
        then UInt256.ofNat 94 else UInt256.ofNat 9800)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = FermatProgram.secp := by decide
  have hv : runInstructions primeValueProgram
      (framed template (UInt256.ofNat 45) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 90)
        (FermatProgram.primeValue modulus :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 })
      [primeValueProgram, FermatProgram.primeValue, runInstructions, framed,
        Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hsecp,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have ht : runInstructions [.push 2 9800, .op .JUMPI]
      (framed template (UInt256.ofNat 90)
        (FermatProgram.primeValue modulus :: modulus :: rest)) =
      some (framed template
        (if (FermatProgram.primeValue modulus).toNat = 0
          then UInt256.ofNat 94 else UInt256.ofNat 9800)
        (modulus :: rest)) := by
    by_cases hp : (FermatProgram.primeValue modulus).toNat = 0 <;>
      simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
        hc1, hc2, htarget, UInt256.isTrue, hp,
        Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod] <;>
      omega
  exact runInstructions_append_some _ _ _ _ _ hv ht

theorem run_jumpTail (template : State) (rest : List UInt256) (hrest : rest.length < 1023)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions jumpTailProgram (framed template (UInt256.ofNat 94) rest) =
    some (framed template (UInt256.ofNat 745) rest) := by
  have hc : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  simp [jumpTailProgram,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,hc,hc1,
    htarget,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail (template : State) (modulus exponent : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (hsmall : (fermatDiff modulus exponent).toNat ≤ 1)
    (hprime : (FermatProgram.primeValue modulus).toNat ≠ 0)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 9818 = true) :
    runInstructions tailProgram
      (framed template (UInt256.ofNat 9800) (modulus :: exponent :: rest)) =
    some (framed template
      (if (fermatDiff modulus exponent).toNat = 0 then UInt256.ofNat 9809 else UInt256.ofNat 9818)
      (modulus :: exponent :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have hmask : UInt256.isZero ({ val := 0 } : UInt256) = UInt256.ofNat 1 := by decide
  have hparity := guardedParity_eq modulus exponent hsmall hprime
  by_cases hz : (fermatDiff modulus exponent).toNat = 0 <;>
    simp (config := { maxSteps := 500000 }) [tailProgram, runInstructions, framed,
      hmask, hparity, htarget, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_inverseGuard (template : State) (modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions inverseGuardProgram (framed template (UInt256.ofNat 9818) (modulus :: rest)) =
    some (framed template
      (if (inverseDiff modulus).toNat = 0 then UInt256.ofNat 9858 else UInt256.ofNat 745)
      (modulus :: rest)) := by
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  by_cases hz : (UInt256.xor FermatProgram.bn modulus).toNat = 0 <;>
    simp [inverseGuardProgram,runInstructions,framed,inverseDiff,htarget,hz,
      Challenge.EvmProof.Stepper.runInstr,UInt256.isTrue,h1,h2,h3,
      Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  fast : WindowTwentyOneBinding.Block artifact fork 24 fastProgram
  join : WindowTwentyOneBinding.Block artifact fork 33 joinProgram
  prime : WindowTwentyOneBinding.Block artifact fork 45 primeProgram
  jumpTail : WindowTwentyOneBinding.Block artifact fork 94 jumpTailProgram
  tail : WindowTwentyOneBinding.Block artifact fork 9800 tailProgram
  result : WindowTwentyOneBinding.Block artifact fork 9809 FermatProgram.returnProgram
  inverseGuard : WindowTwentyOneBinding.Block artifact fork 9818 inverseGuardProgram
  inverse : WindowTwentyOneBinding.Block artifact fork 9858 FixedExponentProgram.program
  genCheck : WindowTwentyOneBinding.Block artifact fork 101 genCheckProgram
  genLoad : WindowTwentyOneBinding.Block artifact fork 112 genLoadProgram
  routeJump : Decode.isValidJumpDest artifact.code 745 = true
  joinJump : Decode.isValidJumpDest artifact.code 33 = true
  bigJump : Decode.isValidJumpDest artifact.code 219 = true
  tailJump : Decode.isValidJumpDest artifact.code 9800 = true
  inverseJump : Decode.isValidJumpDest artifact.code 9818 = true

#print axioms run_prime
#print axioms run_inverseGuard
end Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext
